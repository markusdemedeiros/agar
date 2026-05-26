# Iris-Lean + Std.Do

Prototype integration between Iris-Lean and Std.Do by using the Iris completeness theorem.
(paper: https://simongregersen.com/papers/2026-completeness.pdf)

The dream is that we can reuse some of the large-scale proof automation being developed for shallowly-embedded monadic languages. The working theory is that real libraries will A. have many components that are easy shallowly verify, but B. some components need a high-fidelity model of a program's semantics that is unrealistic to work with shallowly. For the former proofs to be useful they need to link with proofs in the latter context. This prototype does a rudimentary version of that. 

## Example 

See `Agar/Examples/ParChecksum.lean`. The code computes a sum of squares by forking off two threads (each computing half the sum) and then synchronizing with a hot CAS loop. 

You read this example from bottom to top. Here's the main result 
```
theorem parChecksum_closed_concrete
    (Na : Nat) (Nb Nc : Int)
    (h_mid_ne_0 : midVal Na Nb ≠ 0)
    (h_top_ne_0 : topVal Na Nb Nc ≠ 0)
    (h_mid_ne_top : midVal Na Nb ≠ topVal Na Nb Nc) :
    Machine.safe (parChecksumComposite Na Nb Nc)
      (· = Val.int (topVal Na Nb Nc)) :=
  Agar.Logic.parChecksum_closed (GF := GF) (F := PNat) Na Nb Nc
    h_mid_ne_0 h_top_ne_0 h_mid_ne_top

```

This gives us safety and correctness in our deeply-embedded interleaving semantics. We prove it by embedding into Iris. The proof is at `parChecksum_closed` which uses Iris's idioms for allocating invariants and proving thread safety. 

The individual workers are verified in `workerA_spec`/`workerB_spec`. The critical step is the lemma `wp_callee_routeA_generic`: this applies the completeness theorem to exit the Iris logic. Once you do that, you're no longer proving stuff about the Agar `wp`, but back to getting a proof analogous to  `Machine.safe `. The concrete goal is 

```
theorem helper_safeTp_sumSquares (Na : Nat) (Nb Nc : Int)
    (n : Nat) (a : Int) :
    ∀ σ, Machine.SafeTp (parChecksumComposite Na Nb Nc)
        ⟨σ, [sumSquares_init n a]⟩ (sumSquares_post n [Val.int a]) := by
```

This is a pure fact about the operational semantics of a program. 
Any external prover is free to take the reins at this point. 

We'll try to use `Std.Do`, which expects a monadic program.
For a restricted fragment of Agar, that is possible. 

When we do that, we're able to get an actual `Std.Do` obligation!
```
theorem sumSquares_spec (n : Nat) (a : Int) :
    ⦃fun ρ : Env => ⌜ρ "a" = some (Val.int a)⌝⦄
    denoteM (sumSqProg n)
    ⦃⇓ r => fun ρ' : Env =>
      ⌜r = some () ∧ ρ' "acc" = some (Val.int (sumSquaresValue a n))⌝⦄ := by
  intro ρ hpre
```

`mcgen` then helps us handle it in the proof. 

## Limitations

This is not the full completeness result yet, which means our pure code must really be pure, and not deal with state at all. Also, Agar's wacko semantics made some of the denotational stuff hard to figure out (especially as it relates to the program stack). 

The denotational layer is a little clunky still, I think that lining it up with something `mvcgen` is good at needs some hard thought. 

Overall: I expect that a good version of this approach is possible, using the generic `WP` proof presented in the paper. 
