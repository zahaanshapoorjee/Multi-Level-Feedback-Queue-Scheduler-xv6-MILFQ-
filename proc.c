#include "types.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "mmu.h"
#include "x86.h"
#include "proc.h"
#include "spinlock.h"
#include <stdio.h>

struct {
  struct spinlock lock;
  struct proc proc[NPROC];
  uint PromoteAtTime;
} ptable;

static struct proc *initproc;

int nextpid = 1;
extern void forkret(void);
extern void trapret(void);

static void wakeup1(void *chan);

// Creating a 2D array with the each row representing a different priority
struct proc* Queue1[NPROC];
struct proc* Queue2[NPROC];
struct proc* Queue3[NPROC];
struct proc* Queue4[NPROC];

int front1 = -1;
int rear1 = -1;

int front2 = -1;
int rear2 = -1;

int front3 = -1;
int rear3 = -1;

int front4 = -1;
int rear4 = -1;

int isFull(int front, int rear, int size) {
  if ((front == rear + 1) || (front == 0 && rear == size - 1)) return 1;
  return 0;
}

int isEmpty(int front) {
  if (front == -1) return 1;
  return 0;
}

// Adding an element to Queue1
void enQueue1(struct proc* element) {
  if (isFull(front1, rear1, NPROC))
    {}
  else {
    if (front1 == -1) front1 = 0;
    rear1 = (rear1 + 1) % NPROC;
    Queue1[rear1] = element;
  }
}

// Removing an element from Queue1
struct proc* deQueue1() {
  struct proc *element;
  if (isEmpty(front1)) {
    {}
    return NULL;
  } else {
    element = Queue1[front1];
    if (front1 == rear1) {
      front1 = -1;
      rear1 = -1;
    } 
    // Q has only one element, so we reset the 
    // queue after dequeing it. ?
    else {
      front1 = (front1 + 1) % NPROC;
    }
    return (element);
  }
}

// Adding an element to Queue2
void enQueue2(struct proc* element) {
  if (isFull(front2, rear2, NPROC))
    {}
  else {
    if (front2 == -1) front2 = 0;
    rear2 = (rear2 + 1) % NPROC;
    Queue2[rear2] = element;
  }
}

// Removing an element from Queue2
struct proc* deQueue2() {
  struct proc *element;
  if (isEmpty(front2)) {
    {}
    return NULL;
  } else {
    element = Queue2[front2];
    if (front2 == rear2) {
      front2 = -1;
      rear2 = -1;
    } 
    // Q has only one element, so we reset the 
    // queue after dequeing it. ?
    else {
      front2 = (front2 + 1) % NPROC;
    }
    return (element);
  }
}

// Adding an element to Queue3
void enQueue3(struct proc* element) {
  if (isFull(front3, rear3, NPROC))
    {}
  else {
    if (front3 == -1) front3 = 0;
    rear3 = (rear3 + 1) % NPROC;
    Queue3[rear3] = element;
  }
}

// Removing an element from Queue3
struct proc* deQueue3() {
  struct proc *element;
  if (isEmpty(front3)) {
    {}
    return NULL;
  } else {
    element = Queue3[front3];
    if (front3 == rear3) {
      front3 = -1;
      rear3 = -1;
    } 
    // Q has only one element, so we reset the 
    // queue after dequeing it. ?
    else {
      front3 = (front3 + 1) % NPROC;
    }
    return (element);
  }
}

// Adding an element
void enQueue4(struct proc* element) {
  if (isFull(front4, rear4, NPROC))
    {}
  else {
    if (front4 == -1) front4 = 0;
    rear4 = (rear4 + 1) % NPROC;
    Queue4[rear4] = element;
  }
}

// Removing an element
struct proc*deQueue4() {
  struct proc *element;
  if (isEmpty(front4)) {
    {}
    return NULL;
  } else {
    element = Queue4[front4];
    if (front4 == rear4) {
      front4 = -1;
      rear4 = -1;
    } 
    // Q has only one element, so we reset the 
    // queue after dequeing it. ?
    else {
      front4 = (front4 + 1) % NPROC;
    }
    return (element);
  }
}




// Creating a variable to hold the size of the Queues of the various levels to use in promotion
// It will ensure there are not any empty indices in the queues
// and that processes get added to the tail of the required queue
int SizeofQueue[MAXPRIORITY+1] = {0};

void
pinit(void)
{
  initlock(&ptable.lock, "ptable");
}

// Must be called with interrupts disabled
int
cpuid() {
  return mycpu()-cpus;
}

// Must be called with interrupts disabled to avoid the caller being
// rescheduled between reading lapicid and running through the loop.
struct cpu*
mycpu(void)
{
  int apicid, i;
  
  if(readeflags()&FL_IF)
    panic("mycpu called with interrupts enabled\n");
  
  apicid = lapicid();
  // APIC IDs are not guaranteed to be contiguous. Maybe we should have
  // a reverse map, or reserve a register to store &cpus[i].
  for (i = 0; i < ncpu; ++i) {
    if (cpus[i].apicid == apicid)
      return &cpus[i];
  }
  panic("unknown apicid\n");
}

// Disable interrupts so that we are not rescheduled
// while reading proc from the cpu structure
struct proc*
myproc(void) {
  struct cpu *c;
  struct proc *p;
  pushcli();
  c = mycpu();
  p = c->proc;
  popcli();
  return p;
}

//PAGEBREAK: 32
// Look in the process table for an UNUSED proc.
// If found, change state to EMBRYO and initialize
// state required to run in the kernel.
// Otherwise return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;
  char *sp;

  acquire(&ptable.lock);

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == UNUSED)
      goto found;

  release(&ptable.lock);
  return 0;

found:
  p->state = EMBRYO;
  p->pid = nextpid++;
  release(&ptable.lock);

  // Allocate kernel stack.
  if((p->kstack = kalloc()) == 0){
    p->state = UNUSED;
    return 0;
  }
  sp = p->kstack + KSTACKSIZE;

  // Leave room for trap frame.
  sp -= sizeof *p->tf;
  p->tf = (struct trapframe*)sp;

  // Set up new context to start executing at forkret,
  // which returns to trapret.
  sp -= 4;
  *(uint*)sp = (uint)trapret;

  sp -= sizeof *p->context;
  p->context = (struct context*)sp;
  memset(p->context, 0, sizeof *p->context);
  p->context->eip = (uint)forkret;

  return p;
}

//PAGEBREAK: 32
// Set up first user process.
void
userinit(void)
{ 
  struct proc *p;
  extern char _binary_initcode_start[], _binary_initcode_size[];
  ptable.PromoteAtTime = ticks + TICKS_TO_PROMOTE;

  p = allocproc();

  initproc = p;
  if((p->pgdir = setupkvm()) == 0)
    panic("userinit: out of memory?");
  inituvm(p->pgdir, _binary_initcode_start, (int)_binary_initcode_size);
  p->sz = PGSIZE;
  memset(p->tf, 0, sizeof(*p->tf));
  p->tf->cs = (SEG_UCODE << 3) | DPL_USER;
  p->tf->ds = (SEG_UDATA << 3) | DPL_USER;
  p->tf->es = p->tf->ds;
  p->tf->ss = p->tf->ds;
  p->tf->eflags = FL_IF;
  p->tf->esp = PGSIZE;
  p->tf->eip = 0;  // beginning of initcode.S

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  // this assignment to p->state lets other cores
  // run this process. the acquire forces the above
  // writes to be visible, and the lock is also needed
  // because the assignment might not be atomic.
  acquire(&ptable.lock);

  p->state = RUNNABLE;
  p->priority=MAXPRIORITY;
  p->budget= DEFAULT_BUDGET;
  enQueue4(p);
  cprintf("Process userinit initialized and put at Highest Priority Queue. It has Process ID: %d\n", Queue4[front4]->pid);
  release(&ptable.lock);
}

// Grow current process's memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint sz;
  struct proc *curproc = myproc();

  sz = curproc->sz;
  if(n > 0){
    if((sz = allocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  } else if(n < 0){
    if((sz = deallocuvm(curproc->pgdir, sz, sz + n)) == 0)
      return -1;
  }
  curproc->sz = sz;
  switchuvm(curproc);
  return 0;
}

// Create a new process copying p as the parent.
// Sets up stack to return as if from system call.
// Caller must set state of returned proc to RUNNABLE.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *curproc = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy process state from proc.
  if((np->pgdir = copyuvm(curproc->pgdir, curproc->sz)) == 0){
    kfree(np->kstack);
    np->kstack = 0;
    np->state = UNUSED;
    return -1;
  }
  np->sz = curproc->sz;
  np->parent = curproc;
  *np->tf = *curproc->tf;

  // Clear %eax so that fork returns 0 in the child.
  np->tf->eax = 0;

  for(i = 0; i < NOFILE; i++)
    if(curproc->ofile[i])
      np->ofile[i] = filedup(curproc->ofile[i]);
  np->cwd = idup(curproc->cwd);

  safestrcpy(np->name, curproc->name, sizeof(curproc->name));

  pid = np->pid;

  acquire(&ptable.lock);

  np->state = RUNNABLE;
  // Initializing DEFAULT BUDGET and priority for the newly initialised process
  np->budget = DEFAULT_BUDGET;
  np->priority = MAXPRIORITY;
  enQueue1(np);

  release(&ptable.lock);

  return pid;
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait() to find out it exited.
void
exit(void)
{
  struct proc *curproc = myproc();
  struct proc *p;
  int fd;

  if(curproc == initproc)
    panic("init exiting");

  // Close all open files.
  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd]){
      fileclose(curproc->ofile[fd]);
      curproc->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(curproc->cwd);
  end_op();
  curproc->cwd = 0;

  acquire(&ptable.lock);

  // Parent might be sleeping in wait().
  wakeup1(curproc->parent);

  // Pass abandoned children to init.
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->parent == curproc){
      p->parent = initproc;
      if(p->state == ZOMBIE)
        wakeup1(initproc);
    }
  }

  // Jump into the scheduler, never to return.
  curproc->state = ZOMBIE;
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(void)
{
  struct proc *p;
  int havekids, pid;
  struct proc *curproc = myproc();
  
  acquire(&ptable.lock);
  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->parent != curproc)
        continue;
      havekids = 1;
      if(p->state == ZOMBIE){
        // Found one.
        pid = p->pid;
        kfree(p->kstack);
        p->kstack = 0;
        freevm(p->pgdir);
        p->pid = 0;
        p->parent = 0;
        p->name[0] = 0;
        p->killed = 0;
        p->state = UNUSED;
        release(&ptable.lock);
        return pid;
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || curproc->killed){
      release(&ptable.lock);
      return -1;
    }

    // Wait for children to exit.  (See wakeup1 call in proc_exit.)
    sleep(curproc, &ptable.lock);  //DOC: wait-sleep
  }
}

//PAGEBREAK: 42
// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run
//  - swtch to start running that process
//  - eventually that process transfers control
//      via swtch back to the scheduler.

// Commenting this code out and creating the MLFQ scheduler below it
/*
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  c->proc = 0;
  
  for(;;){
    // Enable interrupts on this processor.
    sti();

    // Loop over process table looking for process to run.
    acquire(&ptable.lock);
    for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
      if(p->state != RUNNABLE)
        continue;

      // Switch to chosen process.  It is the process's job
      // to release ptable.lock and then reacquire it
      // before jumping back to us.
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;

      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
    }
    release(&ptable.lock);

  }
}
*/

// Enter scheduler.  Must hold only ptable.lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->ncli, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();
  uint cpu_ticks;

  if(!holding(&ptable.lock))
    panic("sched ptable.lock");
  if(mycpu()->ncli != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(readeflags()&FL_IF)
    panic("sched interruptible");
  intena = mycpu()->intena;


  cpu_ticks = ticks - p->cpu_ticks_in;
  p->budget -= cpu_ticks;
  p->cpu_ticks_total += cpu_ticks;

  if(p->budget <= 0){ 
    if(p->state == RUNNABLE && p->priority !=1){
      if(p->priority == 4 )
      {
        for(int i =0;i<rear4;i++)
        {
            if(Queue4[i]==p) //PROCESS FOUND
            {

                 for (int j = i; j < rear4-1; j++){
                  Queue4[j] = Queue4[j+1]; // Shift left all processes in the queue by 1
                }
              }
              rear4--; // Decrement level 4 priorirty queue size.
              break; //
        }
        
       }
       else if(p->priority == 3 )
       {
        for(int i =0;i<rear3;i++)
        {
            if(Queue3[i]==p) //PROCESS FOUND
            {

                 for (int j = i; j < rear3-1; j++){
                  Queue3[j] = Queue3[j+1]; // Shift left all processes in the queue by 1
                }
              }
              rear3--; // Decrement level 4 priorirty queue size.
              break; //
        }

       }
       else if(p->priority == 2 )
       {
        for(int i =0;i<rear2;i++)
        {
            if(Queue2[i]==p) //PROCESS FOUND
            {

                 for (int j = i; j < rear2-1; j++){
                  Queue2[j] = Queue2[j+1]; // Shift left all processes in the queue by 1
                }
              }
              rear2--; // Decrement level 4 priorirty queue size.
              break; //
        }

       }
    }
}
    
    p->budget = DEFAULT_BUDGET;
    p->priority -= (p->priority !=1) ? 1 : 0;



  swtch(&p->context, mycpu()->scheduler);
  mycpu()->intena = intena;
}


void resetPriority(void)
{
  for(int i=0;i<rear1;i++)
  {
    struct proc *p = deQueue1() ;
    setpriority(p->pid, 2);
    enQueue2(p);
  }
  for(int i=0;i<rear2;i++)
  {
    struct proc *p = deQueue2() ;
    setpriority(p->pid, 3);
    enQueue3(p);
  }
  for(int i=0;i<rear3;i++)
  {
    struct proc *p = deQueue3() ;
    setpriority(p->pid, 4);
    enQueue4(p);
  }
    
}

/*
  THE MLFQ (MILF) SCHEDULER 
*/
void scheduler(void)
{
  struct proc* p;
  struct cpu* c = mycpu();
  c->proc = 0;
  int process_found;

  for(;;){
    // Enable interrupts on this processor.
    sti();
    process_found = 0; // Initialising

    acquire(&ptable.lock);
    // Check whether the priority must be reassigned
    if(ptable.PromoteAtTime <= ticks)
    {
      // Calling the function to redo priority
      resetPriority();
      ptable.PromoteAtTime = ticks + TICKS_TO_PROMOTE;
    }

    // Loop to go through the various Priority levels and call the process to run
    for(int i=MAXPRIORITY-1; i>=0; i--)
    {
    
      if(i==0)
      {
        for(int j=0;j<=rear1;j++)
        {
          if(Queue1[j]->state==RUNNABLE) 
          {
            process_found=1;
            p=Queue1[j];
            break;
          }

        }
      }
      else if(i==1)
      {
        for(int j=0;j<=rear2;j++)
        {
          if(Queue2[j]->state==RUNNABLE) 
          {
            process_found=1;
            p=Queue2[j];
            break;
          }

        }

      }
      else if(i==2)
      {
        for(int j=0;j<=rear3;j++)
        {
          if(Queue3[j]->state==RUNNABLE) 
          {
            process_found=1;
            p=Queue3[j];
            break;
          }

        }
      }
      else if(i==3)
      {
        for(int j=0;j<=rear4;j++)
        {
          if(Queue4[j]->state==RUNNABLE) 
          {
            process_found=1;
            p=Queue4[j];
            break;
          }

        }

      }
    }
    
    if(process_found == 1)
    {
      c->proc = p;
      switchuvm(p);
      p->state = RUNNING;
      swtch(&(c->scheduler), p->context);
      switchkvm();

      // Process is done running for now.
      // It should have changed its p->state before coming back.
      c->proc = 0;
   }


    release(&ptable.lock);
  }
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  acquire(&ptable.lock);  //DOC: yieldlock
  myproc()->state = RUNNABLE;
  sched();
  release(&ptable.lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch here.  "Return" to user space.
void
forkret(void)
{
  static int first = 1;
  // Still holding ptable.lock from scheduler.
  release(&ptable.lock);

  if (first) {
    // Some initialization functions must be run in the context
    // of a regular process (e.g., they call sleep), and thus cannot
    // be run from main().
    first = 0;
    iinit(ROOTDEV);
    initlog(ROOTDEV);
  }

  // Return to "caller", actually trapret (see allocproc).
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  if(p == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
    {
        p->state = RUNNABLE;
        enQueue1(p);
    }
      
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Kill the process with the given pid.
// Process won't exit until it returns
// to user space (see trap in trap.c).
int
kill(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->pid == pid){
      p->killed = 1;
      // Wake process from sleep if necessary.
      if(p->state == SLEEPING)
        p->state = RUNNABLE;
      release(&ptable.lock);
      return 0;
    }
  }
  release(&ptable.lock);
  return -1;
}

//PAGEBREAK: 36
// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [EMBRYO]    "embryo",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  int i;
  struct proc *p;
  char *state;
  uint pc[10];

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    cprintf("%d %s %s", p->pid, state, p->name);
    if(p->state == SLEEPING){
      getcallerpcs((uint*)p->context->ebp+2, pc);
      for(i=0; i<10 && pc[i] != 0; i++)
        cprintf(" %p", pc[i]);
    }
    cprintf("\n");
  }
}

int
setpriority(int pid, int priority)
{
  // We initialise the struct proc and acquire the ptable
  struct proc *p;
  // Check for whether priority is within bounds

  if(priority<0 || priority>MAXPRIORITY)
  {
    cprintf("The specifed priority is out of bounds!");
    return -1;
  }
  // Going through the ptable to find the required processes
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->pid == pid)
    {
      p->priority = priority;
      p->budget = DEFAULT_BUDGET;
      return 0;
    }
  }
  
  cprintf("The process with the specified pid does not exist!");
  return -1;
 
}

int
getpriority(int pid)
{
  struct proc *p;

  acquire(&ptable.lock);

  // Going through the ptable to find the required processes
  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
  {
    if(p->pid == pid)
    { 
      if(p->state!=UNUSED)
      {
      release(&ptable.lock);
      return p->priority;
      }
      else
      {
        release(&ptable.lock);
        return -1;
      }
    }
  }
  cprintf("The process with the specified pid does not exist!");
  return -1;
}
