# Dumb C wishlist
- Build often
- Aggressively use git worktrees and carefully scoped subagents
- Time is not a factor, you have virtually unlimited time
- Your job is to produce a very high quality artifact, suitable as a reference for generations
- Do not trust the PORTING.md of Iris-Lean, it is out of date

## Priority 1. Overall Robustness and Clarity 
- IDEAL: Code is concice
- IDEAL: Code is high-impact
- IDEAL: Code is easy to maintain and extend
- Simplicty is the best
- Code should be self-doccumenting (no long comments)
- Code should follow Iris idioms and make good use of the latest Iris-Lean tactics such as iframe and itrivial (see TACTICS.md)
- KEY PRINCIPLE: Line count is not the only thing that matters
- Large chanins of underscors or implicits often mean that a _definition_ should be modified
- Code should be organized in a way that is very easy to understand

## Priority 2. Ergonimics
- IDEAL: Build out a robust tactic suite similar to other Iris program logics
- IDEAL: Metaprogramming should be concise and eas
- Metaprogramming should be easy to understand. 
- Tactics to help step through Iris proofs 
- Notation should help work to ease understanding

## Proprity 3. Examples
- Focus on examples that showcase the logic
- Examples are there to stress test the logic. Compilation isn't everything, the point is the show that the logic makes it easy.
- Classic conorrency examples are good
- Low-level concurrency examples are awesome
- HOAS style reasoning is allowed
- At least some examples that involve applying the adequacy theorem to get a fully closed proof. 

## Priority 4. Denotational semantics
- Specifically, a monadic semantics for a pure, terminating subset of the language (no concurrency)
- Use standard Lean monads, nothing fancy, nothing custom
- Marquee theorem: for programs with a denotation, their exec corresponds to their denotation




