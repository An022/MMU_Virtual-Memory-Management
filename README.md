# Virtual-Memory-Management (MMU)
A programming lab with professor Hubertus Franke. 

In this lab, we mimic and construct the function of an operating system's virtual memory manager, which uses page table translation to translate the virtual address spaces of several processes onto physical frames.    

The principal counts, but the lab assumes many processes, each with a virtual address space of exactly 64 virtual pages. Paging must be used because the total number of virtual pages in all virtual address spaces may be greater than the number of physical frames in the simulated system.  We support up to 128 physical page frames, but the quantity is variable and determined by a program parameter.
