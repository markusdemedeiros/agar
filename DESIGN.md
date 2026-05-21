# Agar — Language Design

A toy first-order imperative language with single-cell heap, structs, and
unstructured concurrency. Defined in Lean 4 by a small-step operational
semantics over a thread-pool machine. Built to be small enough to prove things
about, expressive enough to encode locks and channels in-language.

## 1. Paradigm

- First-order: procedure names are not values; no closures, no function
  parameters.
- Statement-based: programs are statements, not expressions.
- Two-world state: per-thread environment of locals + a shared heap. The two
  never alias.
- Concurrency: interleaving thread pool, sequential consistency. The only
  atomic primitive that crosses thread boundaries is `cas`.
- Untyped at runtime; type mismatches manifest as stuck states.

## 2. Values

```
Val ::= n : Int
      | b : Bool
      | ℓ : Loc                          -- opaque heap location
      | unit
      | { f₁ = v₁, …, fₙ = vₙ }          -- struct, named fields
```

- `Loc` is opaque: no arithmetic, no ordering exposed to programs.
- Structs are immutable values. Mutating a field of a struct that lives in the
  heap is a load / functional-update / store sequence (see §6).
- Equality is structural and total on `Val`.

## 3. Expressions

Expressions are **pure and total-modulo-typing**. No loads, no allocation, no
side effects.

```
Expr ::= v                          -- value literal
       | x                          -- local variable
       | e ⊕ e | ⊖ e                -- arithmetic / boolean / comparison
       | { f₁ = e₁, …, fₙ = eₙ }    -- struct construction
       | e.f                        -- field projection
       | e with .f := e'            -- functional field update
```

Evaluation is a total function

```
eval : Env → Expr → Option Val
```

returning `none` on unbound variable, type mismatch (`true + 1`), bad field
projection, etc. A statement that needs to evaluate an expression and gets
`none` does not step — the thread is stuck.

## 4. Statements

```
Stmt ::= skip
       | x := e
       | x := *e                    -- load whole cell
       | *e := e'                   -- store whole cell
       | x := alloc e               -- single cell, initialised to e
       | free e
       | x := cas e e_old e_new     -- atomic; returns the old cell value
       | s ; s'
       | if e then s else s'
       | while e do s
       | x := call f(e₁, …, eₙ)     -- procedure call, result bound to x
       | return e
       | fork f(e₁, …, eₙ)          -- spawn thread running call to f
```

Notes:

- `fork` is *strict*: its argument is syntactically a procedure call. There is
  no `fork s` for arbitrary statements. Inline code that wants to fork must be
  packaged as a procedure first.
- `cas` returns the old value, not a success bit. Callers can compare the
  returned value to `e_old` to decide whether the swap happened.
- There is no discard form for `call`; if the caller does not want the result,
  it binds to a throwaway local.

## 5. Procedures and programs

```
Proc    = { params : List Name, body : Stmt }
Program = { procs : Name → Option Proc, main : Stmt }
```

- The procedure table is static. Recursion (including mutual recursion) is
  allowed because the table is resolved by name at each call.
- Parameters are bound by value into a fresh local environment on entry.
- A procedure body runs to either `return e` or fall-through. Fall-through
  returns `unit`.
- There are no globals. Cross-procedure and cross-thread communication must
  go through (a) procedure parameters and (b) the heap.

## 6. Heap model

- `Mem` is a finite association list of `(Loc, Val)` cells. Operations
  maintain the invariant that each `Loc` appears at most once, so the heap's
  domain is always a finite set of locations. A location not in the list is
  unallocated (or freed).
- `alloc` picks any `Loc` not currently in the domain and binds it to the
  initial value. The choice is genuinely nondeterministic: the per-thread step
  function takes an `Option Loc` parameter, and the machine-level step relation
  existentially quantifies that location. Programs may not depend on which
  address they receive.
- Loads, stores, and CAS operate on whole cells. There is no field-level heap
  addressing.
- `free p` removes `p` from the heap.
- Use-after-free (load / store / cas / free on an unallocated location) is
  **stuck**. Not undefined behaviour, not a trap — the thread simply has no
  step from that state.

Consequence: structs in shared heap cells are racy at the field level. A
field-update pattern

```
x := *p;
*p := x with .f := v
```

is two steps. Another thread can interleave between them. The only atomic
operation on a shared cell is `cas` on the whole cell. Lock-protected access
is the idiomatic pattern; we will write the locks in Agar itself.

## 7. Threads and the machine

```
Frame        = { retVar : Name, cont : Stmt, env : Env }
ThreadState  = { stmt : Stmt, env : Env, stack : List Frame }
MachineState = { heap : Heap, threads : List ThreadState }
```

- Each thread carries its own explicit call stack. Frames are *not* on the
  heap.
- A `call` pushes a new frame `{ retVar = x, cont = <rest of caller>, env =
  <caller env> }`, switches `stmt` to the callee body, and rebinds `env` to a
  fresh map of parameters.
- A `return e` pops the top frame, plugs the returned value into the frame's
  `retVar` in the frame's `env`, and resumes with the frame's `cont`.
- Fall-through (current `stmt` reduced to `skip` while the stack is non-empty)
  behaves like `return unit`.
- A `fork f(args)` adds a new `ThreadState` whose `stmt` is the body of `f`,
  whose `env` binds the parameters, and whose `stack` is empty. The forked
  thread terminates when *its initial frame* returns (or falls through), at
  which point the thread is removed. There is no join.
- Initial machine state: one thread containing `main`, empty env, empty stack.

The small-step relation has the shape

```
(heap, threads) → (heap', threads')
```

and is defined by:

1. Pick any non-terminated thread `t = threads[i]`.
2. Take one local step `(heap, t) →ₜ (heap', t')`.
3. If `t'` is terminated, drop it from the pool; otherwise replace.
4. If a `fork` fired, append the new thread.

A thread is *terminated* when its `stmt` is `skip` and its `stack` is empty.

## 8. Termination, halting, stuckness

- The `main` thread terminating (or executing `return e` at the top level)
  halts the whole machine, regardless of what other threads are doing.
- Any thread can become stuck: bad expression evaluation, use-after-free, call
  to an undefined procedure, arity mismatch, `cas` on an unallocated cell.
  Stuck threads remain in the pool but contribute no further steps. Other
  threads continue.
- Total deadlock = the whole pool is either terminated or stuck.

## 9. Atomicity inventory

Each of these is one step:

- expression-driven assignment to a local
- load, store, alloc, free
- cas (compare and swap, atomic by construction)
- call (push frame), return (pop frame)
- fork (append thread)
- branch test for `if`, guard test for `while`
- `skip` sequencing (`skip ; s` → `s`)

CAS is the only construct that combines a read and a write into one step. All
other read-modify-write patterns require multiple steps and are therefore
visible to interleavings.

## 10. Out of scope for v1

- No closures, function values, or higher-order procedures.
- No pointer arithmetic.
- No per-field heap addressing.
- No relaxed memory, no fences.
- No join, channels, or built-in locks — these are derived in-language.
- No globals.
- No static type system; ill-typed programs get stuck at runtime.

## 11. File layout (planned)

- `Agar/Syntax.lean` — `Val`, `Expr`, `Stmt`, `Proc`, `Program`.
- `Agar/Semantics.lean` — environments, heap, frames, thread state, machine
  state, the small-step relation.
- `Agar/Examples.lean` — small programs: counter, spinlock, producer /
  consumer.

Later (v2+, not committed): a well-formedness predicate, a notion of safe
execution, metatheoretic lemmas (determinism per thread, progress modulo
stuck-ness), and possibly a surface syntax / parser.
