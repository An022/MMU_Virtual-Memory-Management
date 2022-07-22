#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <stdlib.h>
#include <stdint.h>
#include <string>
#include <iostream>
#include <fstream>
#include <deque>
#include <vector>

using namespace std;

#define MAX_VPAGES 64
#define MAX_FRAMES 128
#define MAX_PROCESSES 10
#define INSTRUCTION_ROUND 50

int instCounter = 0;

struct vma {
  int svp;
  int evp;
  int wProtected;
  int fMap;
};

struct Inst {
  char inChar;
  int inNum;
};

struct pte_t {
  unsigned int PRESENT:1;
  unsigned int REFERENCED:1;
  unsigned int MODIFIED:1;
  unsigned int WRITE_PROTECTED:1;
  unsigned int PAGEOUT:1;
  unsigned int FRAMES:7;
  unsigned int PAGENO:7;
  unsigned int FILEMAPPED:1;
};

struct frame_t {
  pte_t* vpage;
  int proID;
  int frameID;
  uint32_t age;
  uint32_t timeLast; //time last use
};

struct proState {
  int unmaps;
  int maps;
  int ins;
  int outs;
  int fins;
  int fouts;
  int zeros;
  int segv;
  int segprot;
};

class Process {
public:
  int proID;
  vector <vma*> vmas; 
  pte_t page_table[MAX_VPAGES];
  proState* pstate;

  Process(int pid) {
    this->proID = 0;
    memset(page_table, 0, MAX_VPAGES*sizeof(pte_t));
    pstate = new proState();
  }

  void printPT() {
    printf("PT[%d]:", proID);
    for (int i = 0; i < MAX_VPAGES; i++) {
      if(!page_table[i].PRESENT) {
        if (page_table[i].PAGEOUT) {
          printf(" #");
        }
        else {
          printf(" *");
        }
      }
      else {
        printf(" %d:%c%c%c", i, (page_table[i].REFERENCED ? 'R' : '-'), 
                                (page_table[i].MODIFIED ? 'M' : '-'), 
                                (page_table[i].PAGEOUT ? 'S' : '-'));
      }
    }
    printf("\n");
  }

  void printSUM() {
    printf ("PROC[%d]: U=%d M=%d I=%d O=%d FI=%d FO=%d Z=%d SV=%d SP=%d\n", 
              proID, pstate->unmaps, pstate->maps, pstate->ins, 
              pstate->outs, pstate->fins, pstate->fouts, 
              pstate->zeros, pstate->segv, pstate->segprot);
  }
};

vector <int> rNums;
vector <Inst> instList;
vector <Process*> proList;
deque <frame_t*> frameList;
frame_t frame_table[MAX_FRAMES];

// ========== RANDOM NUMBER ==========
int n_counter;

void readRfile (string rFile) {
  fstream file (rFile.c_str());
  string line;
  int rVal;
  if (file.is_open()) {
    while (getline(file, line) && !file.eof()) {
      sscanf (line.c_str(), "%d", &rVal);
      rNums.push_back(rVal);
    }
  }
}

int getRnums (int rSize) {
  return (rNums[++n_counter] % rSize);
}

class Pager {
public:
  int hand;
  int num_frames;
  // virtual base class
  virtual frame_t* select_victim_frame() = 0; 
};

class FIFO : public Pager {
public:
  int hand;
  int num_frames;

  FIFO(int max_frames) {
    hand = 0;
    num_frames = max_frames;
  }

  frame_t* select_victim_frame() {
    frame_t* frame = &frame_table[hand];
    hand = (++hand) % num_frames;
    return frame;
  }
};

class Random : public Pager {
public:
  int num_frames;

  Random(int max_frames) {
    num_frames = max_frames;
  }
  
  frame_t* select_victim_frame() {
    return &frame_table[getRnums(num_frames)];
  }
};

class Clock : public Pager {
public:
  int hand;
  int num_frames;

  Clock (int max_frames) {
    hand = 0;
    num_frames = max_frames;
  }

  frame_t* select_victim_frame() {
    while(true) {
      frame_t* frame = &frame_table[hand];
      hand = (++hand) % num_frames;
      if (!frame->vpage->REFERENCED) return frame;
      frame->vpage->REFERENCED = 0;
    }
  }
};

class ESC : public Pager {
public:
  int hand;
  int num_frames;
  int last_reset;
  int class_index;
  int low_class;
  int low_hand;

  ESC (int max_frames) {
    hand = 0;
    num_frames = max_frames;
    last_reset = 0;
  }

  frame_t* select_victim_frame() {
    low_class = 4;
    frame_t* frame = NULL;

    for (int i = 0; i < num_frames; ++i) {
      // current frame and compute class_index
      frame = &frame_table[hand];
      class_index = 2 * frame->vpage->REFERENCED + frame->vpage->MODIFIED;

      //update the lowest
      if (class_index < low_class) {
        low_class = class_index;
        low_hand = hand;
      }
      
      hand = (++hand) % num_frames;

      // If 50 or more instructions have passed since the last time the reference bits were reset
      if (instCounter - last_reset >= INSTRUCTION_ROUND) {
        frame->vpage->REFERENCED = 0;
      }
      //when a frame for class-0 (R=0,M=0) is encountered, you should stop the scan
      else if (low_class == 0) break;
    }

    // update the last_reset
    if (instCounter - last_reset >= INSTRUCTION_ROUND) last_reset = instCounter;

    //Once a victim frame is determined, the hand is set to the next position after the victim frame for the next select_victim_frame() invocation.
    if (low_hand+1 == num_frames) {
      hand = 0;
    }
    else {
      hand = low_hand+1;
    }

    return &frame_table[low_hand];
  }
};

class Aging : public Pager {
public:
  int hand;
  int num_frames;
  int low_hand;

  Aging (int max_frames) {
    hand = 0;
    num_frames = max_frames;
  }

  frame_t* select_victim_frame() {
    frame_t* frame = NULL;
    //  0xFFFFFFFF is equivalent to the decimal value of "-1"
    uint32_t low_age = 0xffffffff;

    for (int i = 0; i < num_frames; ++i) {
      frame = &frame_table[hand];
      // first aging
      frame->age = frame->age >> 1;
      frame->age = frame->vpage->REFERENCED? frame->age | 0x80000000 : frame->age;
      frame->vpage->REFERENCED = 0;

      if (frame->age < low_age) {
        low_age = frame->age;
        low_hand = hand;
      }
      hand = (++hand) % num_frames;
    }

    if (low_hand+1 == num_frames) {
      hand = 0;
    }
    else {
      hand = low_hand+1;
    }

    return &frame_table[low_hand];
  }
};

class WS : public Pager {
public:
  int hand;
  int num_frames;

  WS (int max_frames) {
    hand = 0;
    num_frames = max_frames;
  }

  frame_t* select_victim_frame() {
    frame_t* frame = NULL;
    // max of the decimal value
    uint32_t low_time = UINT32_MAX;
    unsigned int min_R_bit = 1;
      int low_hand = hand;
    
    for (int i = 0; i < num_frames; ++i) {
      frame = &frame_table[hand];
      if (frame->vpage->REFERENCED) {
        frame->vpage->REFERENCED = 0;
        frame->timeLast = instCounter - 1;
      }
      else if ((instCounter - 1) - frame->timeLast >= INSTRUCTION_ROUND) {
          low_hand = hand;
          break;
      }
      else if (frame->timeLast < low_time) {
            low_time = frame->timeLast;
            low_hand = hand;
      }
      hand = (++hand) % num_frames;
    }

    if (low_hand+1 == num_frames) {
      hand = 0;
    }
    else {
      hand = low_hand+1;
    }
    return &frame_table[low_hand];
  }
};

class MMU {
int numFrames;
bool O_flag;
bool P_flag;
bool F_flag;
bool S_flag;

Pager* currPager;

public:
  MMU(int frames, char pager, bool OFlag, bool PFlag, bool FFlag, bool SFlag) { 
    numFrames = frames;
    O_flag = OFlag;
    P_flag = PFlag;
    F_flag = FFlag;
    S_flag = SFlag;

    //Initialize all frames in the free list
    for(int i = 0; i < numFrames; ++i) {
      memset(&frame_table[i], 0, sizeof(frame_t));
      frame_table[i].frameID = i;
      frameList.push_back(&frame_table[i]);
    }
    // Choose algo
    switch (pager) {
      case 'f':
        currPager = new FIFO (numFrames);
        break;
      case 'r':
        currPager = new Random(numFrames);
        break;
      case 'c':
        currPager = new Clock(numFrames);
        break;
      case 'e':
        currPager = new ESC(numFrames);
        break;
      case 'a':
        currPager = new Aging(numFrames);
        break;
      case 'w':
        currPager = new WS(numFrames);
        break;
    }
  }

  frame_t* allocate_frame_from_free_list(){
    frame_t* frame = NULL;
      if(frameList.size() > 0){
        frame = frameList.front();
        frameList.pop_front();
      }
      return frame;
  }

  frame_t* get_frame() {
    frame_t *frame = allocate_frame_from_free_list();
    if (frame == NULL){
      frame = currPager->select_victim_frame();
      if(O_flag) printf(" UNMAP %d:%d\n",frame->proID, frame->vpage->PAGENO);
      proList[frame->proID]->pstate->unmaps++;
      frame->vpage->PRESENT = 0;
      if(frame->vpage->MODIFIED){
        if(frame->vpage->FILEMAPPED){
          if(O_flag) printf(" FOUT\n");
          proList[frame->proID]->pstate->fouts++;
        }
        else{
          if(O_flag) printf(" OUT\n");
          proList[frame->proID]->pstate->outs++;
          frame->vpage->PAGEOUT = 1;
        }
      }
    }
    frame->age = 0;
    frame->timeLast = instCounter-1;
    frame->vpage = NULL;
    frame->proID = -1;
    return frame;
  }

  bool pgfault_handler (Process* pro, pte_t* pte, int vpage) {
    int v = vpage;
    for (int i = 0; i < pro->vmas.size(); ++i) {
      if (v >= pro->vmas[i]->svp && v <= pro->vmas[i]->evp) {
        pte->FILEMAPPED = pro->vmas[i]->fMap;
        pte->WRITE_PROTECTED = pro->vmas[i]->wProtected;
        pte->PAGENO = v;
        return true;
        break;
      }
    }
    return false;
  }
  void printFT() {
    printf("FT:");
    for (int i = 0; i < numFrames; ++i) {
      if (frame_table[i].vpage) {
        if ((frame_table[i].vpage)->PRESENT) {
          printf(" %d:%d", frame_table[i].proID,(frame_table[i].vpage)->PAGENO);
        }
      }
      else printf(" *");
    }
    printf("\n");
  }
};

// ========== READ FILE ==========
void readIfile (string iFile) {
  fstream file (iFile.c_str());
  string line;
  Inst currInst;
  vma* vma_spec;
  char inChar;
  int inNum;
  int pVal = 0;
  int numPros = 0; // numbers of processes
  int vmasVal = 0;
  int proID = 0;
  int svp = 0;
  int evp = 0;
  int wProtected = 0;
  int fMap = 0;

  if (file.is_open()) {
    while(getline(file, line) && !file.eof()) {
      if (line.empty()||line[0]=='#') {
        continue;
      }
      if (isdigit(line[0])) {
        sscanf(line.c_str(), "%d", &numPros);
        for (int i = 0 ; i < numPros; ++i) {
          getline(file, line);
          if (line[0]=='#') {
            i--;
            continue;
          }
          Process* currPro = new Process(i);
          currPro->proID = i;
          proList.push_back(currPro);
          sscanf(line.c_str(), "%d", &vmasVal);
          for (int j = 0; j < vmasVal; ++j) {
            getline(file, line);
            if (line[0] != '#') {
              vma_spec = new vma();
              sscanf(line.c_str(), "%d %d %d %d", &vma_spec->svp, &vma_spec->evp, &vma_spec->wProtected, &vma_spec->fMap);
              proList[i]->vmas.push_back(vma_spec);
            }
          }
        }
      }
      else {
        sscanf(line.c_str(), "%c %d", &inChar, &inNum);
        currInst.inChar = inChar;
        currInst.inNum  = inNum;
        instList.push_back(currInst);
      }
    }
  }
}

// ========== Initialization ========== 
bool get_next_instruction(char* operation, int* vpage){
  while(!instList.empty()) {
    Inst currInst;
    currInst = instList.front();
    *operation = currInst.inChar;
    *vpage = currInst.inNum;
    instList.erase(instList.begin());
    return true;
  }
  return false;
}

void update_pte (pte_t* pte, int rw) {
  if (rw == 1) {
    pte->MODIFIED = 1;
  }
  else {
    pte->REFERENCED = 1;
  }
}

void simulation(MMU* mmu, bool OFlag, bool PFlag, bool FFlag, bool SFlag) {
  char instruction;
  int vpage;
  int cost = 0;
  int ctx_switches = 0;
  int process_exits = 0;
  Process* currProcess;

  while (get_next_instruction(&instruction, &vpage)) {
    if(OFlag) {
      printf("%d: ==> %c %d\n", instCounter, instruction, vpage);
    }
    instCounter++;
    //hadle special case 'c' and 'e' instruction
    if (instruction == 'c') {
      ctx_switches++;
      currProcess = proList[vpage];
    }
    else if (instruction == 'e') {
      process_exits++;
      printf("EXIT current process %d\n", currProcess->proID);
      for(int i=0; i < MAX_VPAGES; i++){
        if(currProcess->page_table[i].PRESENT){
          if(OFlag) printf(" UNMAP %d:%d\n",currProcess->proID, currProcess->page_table[i].PAGENO);
          currProcess->pstate->unmaps++;
          if(currProcess->page_table[i].MODIFIED && currProcess->page_table[i].FILEMAPPED){
            if(OFlag) printf(" FOUT\n");
            currProcess->pstate->fouts++;
          }
          // reset frame_table
          frame_table[currProcess->page_table[i].FRAMES].proID = -1;
          frame_table[currProcess->page_table[i].FRAMES].vpage = NULL;
          frame_table[currProcess->page_table[i].FRAMES].age = 0;
          frame_table[currProcess->page_table[i].FRAMES].timeLast = 0;
          frameList.push_back(&frame_table[currProcess->page_table[i].FRAMES]);
        }
        // reset currProcesss' condition
        currProcess->page_table[i].PRESENT = 0;
        currProcess->page_table[i].MODIFIED = 0;
        currProcess->page_table[i].REFERENCED = 0;
        currProcess->page_table[i].PAGEOUT = 0;
        currProcess->page_table[i].FRAMES = 0;
      }
      currProcess = NULL;
    }
    // for the 'r' and 'w'
    else {
      pte_t* pte = &currProcess->page_table[vpage];
      if (!pte->PRESENT) {
        if(!mmu->pgfault_handler(currProcess, pte, vpage)){
          if(OFlag) printf(" SEGV\n");
          currProcess->pstate->segv++;
          continue;
        }
        frame_t* newFrame = mmu->get_frame();
        newFrame->vpage = pte;
        newFrame->proID = currProcess->proID;
        if (pte->PAGEOUT) {
          if (OFlag) printf(" IN\n");
          currProcess->pstate->ins++;
        }
        else if (pte->FILEMAPPED) {
          if (OFlag) printf (" FIN\n");
          currProcess->pstate->fins++;
        }
        else {
          if (OFlag) printf (" ZERO\n");
          currProcess->pstate->zeros++;
        }
        if (OFlag) printf(" MAP %d\n", newFrame->frameID);
        currProcess->pstate->maps++;
        pte->MODIFIED = 0;
        pte->REFERENCED = 0;
        pte->FRAMES = newFrame->frameID;
        pte->PRESENT = 1;
      }
      // check write protection
      update_pte(pte, 0);
      if (instruction == 'w') {
        if (pte->WRITE_PROTECTED) {
          currProcess->pstate->segprot++;
          if (OFlag) printf(" SEGPROT\n");
        }
        else {
          update_pte(pte, 1);
        }
      }
    }
  }
  // print pagetable
  if (PFlag) {
    for (int i = 0; i < proList.size(); ++i) {
      proList[i]->printPT();
    }
  }
  // print frame table
  if (FFlag) mmu->printFT();

  // print summary
  if (SFlag) {
    for (int i = 0; i < proList.size(); ++i) {
      proList[i]->printSUM();
    }
  }

  // print cost
  cost += ctx_switches*130;
  cost += process_exits*1250;
  cost += (instCounter - ctx_switches - process_exits);
  for(int i=0; i < proList.size(); ++i){
    cost += proList[i]->pstate->maps*300;
    cost += proList[i]->pstate->unmaps*400;
    cost += proList[i]->pstate->ins*3100;
    cost += proList[i]->pstate->outs*2700;
    cost += proList[i]->pstate->fins*2800;
    cost += proList[i]->pstate->fouts*2400;
    cost += proList[i]->pstate->zeros*140;
    cost += proList[i]->pstate->segv*340;
    cost += proList[i]->pstate->segprot*420;
  }
  if (SFlag) printf("TOTALCOST %d %d %d %d %lu\n", instCounter, ctx_switches, process_exits, cost, sizeof(pte_t));
}


int main(int argc, char* argv[]) {
  bool OFlag = false;
  bool PFlag = false;
  bool FFlag = false;
  bool SFlag = false;
  int num_frames;
  char c;
  char algo;

  while ((c = getopt(argc, argv, "f:a:o:")) != -1) {
    switch (c) {
      case 'f':
        num_frames = atoi(optarg);
        if(num_frames == 0){
          return -1;
        }
        else if(num_frames < 0 || num_frames > MAX_FRAMES){
          return -1;
        }
        break;

      case 'a':
        if(!optarg || (*optarg != 'f' && *optarg != 'r' && *optarg != 'c' && *optarg != 'e' && *optarg != 'a' && *optarg != 'w')){
          return -1;
        }
        algo = *optarg;
        break;
      
      case 'o':
        for (int i = 0; i < strlen(optarg); ++i) {
          switch (optarg[i]) {
            case 'O':
              OFlag = true;
              break;
            case 'P':
              PFlag = true;
              break;
            case 'F':
              FFlag = true;
              break;
            case 'S':
              SFlag = true;
              break;
          }
        }
        break;
      case '?':
        return -1;
      default: printf("Invalid Arguments!");
      return -1;
    }
  } 

  setvbuf(stdout, NULL, _IONBF, 0);
  if (argc < 3) {
    cout << "wrong input !" << endl; 
    return 0;
  }
  readRfile(argv[argc-1]);
  readIfile(argv[argc-2]);
  MMU* mmu = new MMU(num_frames, algo, OFlag, PFlag, FFlag, SFlag);
  simulation(mmu, OFlag, PFlag, FFlag, SFlag);
  return 0;
}