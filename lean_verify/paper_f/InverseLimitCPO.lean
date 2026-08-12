import EmbeddingProjection

/-!
# The inverse limit of a tower of ω-CPOs

`WALLS.md` §W8.0 lists three ingredients for `D∞`. `EmbeddingProjection.lean` supplied item 1 and
the function-space functor. This file is **item 2**:

> *"The inverse limit of a tower of ω-CPOs along such pairs, with its ω-CPO structure. This is the
> substantial one, and it is genuinely absent — Mathlib has direct limits of directed systems of
> types, and nothing in the other direction for ordered structures."*

> **`Tower`** — a family `D : ℕ → Type` of ω-CPOs with an embedding–projection pair between each
> consecutive pair of levels.
>
> **`Limit T`** — the coherent sequences: `x : ∀ n, D n` with `proj n (x (n+1)) = x n`. Ordered
> pointwise, and **an ω-CPO**, with suprema computed level by level. The coherence condition
> survives the supremum because each `proj n` is continuous, which is the whole reason the tower is
> built out of *continuous* maps.
>
> **`proj T n : Limit T →𝒄 D n`** — the limit's own projections, continuous by construction, with
> `proj_succ` recording that they commute with the tower's maps.
>
> **`up`, `down`, `down_up`** — travelling `n` levels up the tower and back down is the identity.
>
> **`embFun`, `embSeq_coherent`, `proj_embFun` — AND THE LEVEL-INTO-LIMIT EMBEDDING ITSELF, which
> this header used to say was not built here.** Added 2026-08-11 under `PROOF_STRATEGY` §7 rule 2
> (*finish every unfinished chain*). The deferral was on the grounds that the coherent sequence
> *"needs transport along `k + (n - k) = n` … index bookkeeping rather than mathematics"*. **That
> was right about the difficulty and wrong about it being unavoidable**: `upTo` and `downTo`
> recurse on the TARGET index with the inequality carried as a hypothesis, so the only transport
> left is along a decidable equality of naturals in the one case `k = n+1`, and `omega` discharges
> the arithmetic. See §5.

## What this does NOT do

**The bilimit theorem is not proved, not attempted, and DELIBERATELY NOT NAMED AS A `def` HERE.**
A first draft of this file did name it, as *"for every tower whose levels are equivalent to the
continuous self-maps of the level below, the limit is equivalent to its own continuous self-maps"*.
**That is not the theorem.** The bilimit theorem is about the tower whose steps ARE
`EPPair.funPair` of the steps below — a tower with arbitrary pairs between levels that merely
happen to be function spaces has no reason to have the property. Writing the weaker sentence and
calling it the gap is `ERRATUM 108` exactly, and `ERRATUM 89` is the rule against naming an object
before the modelling choice inside it has been made.

**What would have to be stated first** is the canonical tower: `D₀` a *pointed* ω-CPO,
`Dₙ₊₁ = Dₙ →𝒄 Dₙ`, `step 0` the pair that embeds a point as a constant function and projects by
evaluating at the bottom element, and `step (n+1) = funPair (step n)`. That needs a bottom element,
which `OmegaCompletePartialOrder` does not carry, so it needs `OrderBot` alongside. **Not built
here.** Once it exists the bilimit is statable, and only then.

**Having a limit is not having `D∞`.** This file builds limits of arbitrary towers; `D∞` is the
limit of one particular tower together with a theorem about it, and only the first half is here.
-/

namespace InverseLimitCPO

open OmegaCompletePartialOrder EmbeddingProjection

universe u

/-- **A tower of ω-CPOs**: a level at every natural number, with an embedding–projection pair from
each level into the next. -/
structure Tower where
  /-- The levels. -/
  carrier : ℕ → Type u
  /-- Each level is an ω-CPO. -/
  cpo : ∀ n, OmegaCompletePartialOrder (carrier n)
  /-- And consecutive levels are related by an embedding–projection pair. -/
  step : ∀ n, @EPPair (carrier n) (carrier (n + 1)) (cpo n) (cpo (n + 1))

attribute [instance] Tower.cpo

variable (T : Tower.{u})

/-- **THE INVERSE LIMIT**: coherent sequences through the tower. -/
def Limit : Type u := { x : ∀ n, T.carrier n // ∀ n, (T.step n).proj (x (n + 1)) = x n }

namespace Limit

instance : PartialOrder (Limit T) where
  le x y := ∀ n, x.1 n ≤ y.1 n
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ n := le_trans (h₁ n) (h₂ n)
  le_antisymm x y h₁ h₂ := Subtype.ext (funext fun n => le_antisymm (h₁ n) (h₂ n))

theorem le_iff {x y : Limit T} : x ≤ y ↔ ∀ n, x.1 n ≤ y.1 n := Iff.rfl

/-- The chain of `n`-th components of a chain of coherent sequences. -/
def levelChain (c : Chain (Limit T)) (n : ℕ) : Chain (T.carrier n) where
  toFun i := (c i).1 n
  monotone' _ _ h := (c.monotone h) n

/-- **THE COHERENCE CONDITION SURVIVES THE SUPREMUM**, because each projection is continuous.
This is the one place the tower's maps being *continuous* rather than merely monotone is used, and
it is the reason the construction works at all. -/
theorem levelChain_coherent (c : Chain (Limit T)) (n : ℕ) :
    (T.step n).proj (ωSup (levelChain T c (n + 1))) = ωSup (levelChain T c n) := by
  rw [(T.step n).proj.ωScottContinuous.map_ωSup]
  congr 1
  apply OrderHom.ext
  funext i
  exact (c i).2 n

instance : OmegaCompletePartialOrder (Limit T) where
  ωSup c := ⟨fun n => ωSup (levelChain T c n), levelChain_coherent T c⟩
  le_ωSup c i n := le_ωSup (levelChain T c n) i
  ωSup_le c x h n := ωSup_le (levelChain T c n) (x.1 n) fun i => h i n

theorem ωSup_apply (c : Chain (Limit T)) (n : ℕ) :
    (ωSup c).1 n = ωSup (levelChain T c n) := rfl

end Limit

/-! ## The limit's projections -/

/-- **The limit's `n`-th projection**, continuous by construction: both the order and the suprema
on `Limit` are level-by-level, so reading off a level is a continuous map. -/
def proj (n : ℕ) : Limit T →𝒄 T.carrier n where
  toFun x := x.1 n
  monotone' _ _ h := h n
  map_ωSup' _ := rfl

/-- The projections commute with the tower's own maps, which is what makes them *the* limit's
projections rather than an unrelated family. -/
theorem proj_succ (n : ℕ) (x : Limit T) : (T.step n).proj (proj T (n + 1) x) = proj T n x :=
  x.2 n

/-! ## Each level embeds in the limit

A coherent sequence is determined by a level together with a rule for everything above it. Going
up uses the tower's embeddings and going down its projections; the composite of `n` steps up and
`n` steps down is the identity, so a level really does sit inside the limit as a retract. -/

/-- `n` steps up the tower from level `k`. -/
def up (k : ℕ) : ∀ n, T.carrier k → T.carrier (k + n)
  | 0, x => x
  | n + 1, x => (T.step (k + n)).emb (up k n x)

/-- `n` steps down from level `k + n`. -/
def down (k : ℕ) : ∀ n, T.carrier (k + n) → T.carrier k
  | 0, x => x
  | n + 1, x => down k n ((T.step (k + n)).proj x)

/-- **DOWN UNDOES UP EXACTLY**, by induction on the number of steps and `proj_emb` at each. -/
theorem down_up (k : ℕ) : ∀ n (x : T.carrier k), down T k n (up T k n x) = x
  | 0, _ => rfl
  | n + 1, x => by
    change down T k n ((T.step (k + n)).proj ((T.step (k + n)).emb (up T k n x))) = x
    rw [(T.step (k + n)).proj_emb]
    exact down_up k n x

/-! ## What remains -/

/-- **`Tower` IS INHABITED**, checked rather than assumed: every level the same ω-CPO, every step
the identity pair. **Not** a witness for anything about `D∞` — its levels are not function spaces
— but a structure with three fields deserves an instance before a file is written about it, which
is the standard `AlgebraicCurvature.lean` set for itself this morning. -/
def constTower (D : Type u) [OmegaCompletePartialOrder D] : Tower.{u} where
  carrier _ := D
  cpo _ := inferInstance
  step _ := EPPair.refl

/-- **AND ITS LIMIT IS `D`**, so `Limit` computes something recognisable on the one tower this file
builds. A coherent sequence over the constant tower has `x (n+1) = x n` at every level, because
every projection is the identity, so it is a constant sequence. The docstring above claimed this
in passing; it is a theorem instead. -/
def limitConstEquiv (D : Type u) [OmegaCompletePartialOrder D] :
    Limit (constTower D) ≃ D where
  toFun x := x.1 0
  invFun d := ⟨fun _ => d, fun _ => rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    induction n with
    | zero => rfl
    | succ k ih => exact ih.trans (x.2 k).symm
  right_inv _ := rfl


/-! ## 5. Each level embeds in the limit

**The leg this file deferred**, built 2026-08-11 (`PROOF_STRATEGY` §7 rule 2). The obstacle named in
the header was transport along `k + (n - k) = n`. It is avoided by recursing on the **target** index
with the inequality carried as a hypothesis: `upTo k n h` climbs from `k` to `n`, `downTo n k h`
descends, and neither mentions a subtraction. The one place a transport survives is the case
`k = n + 1`, where it is along a decidable equality of naturals.

**§6 CLIMBS THE RUNG THIS SECTION NAMED.** The paragraph here used to read: *"`embFun` is proved
monotone, not continuous … it is expected to go through, but it is not proved here."* It is proved
now — `upTo_ωSup`, `downTo_ωSup` and `embHom` — and the expectation was correct, which is worth
recording because this file's estimates have not always been. -/

def upTo (k : ℕ) : ∀ n, k ≤ n → T.carrier k → T.carrier n
  | 0, h, x => (Nat.le_zero.1 h) ▸ x
  | n + 1, h, x =>
      if hk : k = n + 1 then hk ▸ x
      else (T.step n).emb (upTo k n (Nat.lt_succ_iff.1 (lt_of_le_of_ne h hk)) x)

def downTo (n : ℕ) : ∀ k, n ≤ k → T.carrier k → T.carrier n
  | 0, h, x => (Nat.le_zero.1 h) ▸ x
  | k + 1, h, x =>
      if hk : n = k + 1 then hk ▸ x
      else downTo n k (Nat.lt_succ_iff.1 (lt_of_le_of_ne h hk)) ((T.step k).proj x)

theorem upTo_self (k : ℕ) (h : k ≤ k) (x : T.carrier k) : upTo T k k h x = x := by
  cases k with
  | zero => rfl
  | succ n => simp [upTo]

theorem downTo_self (k : ℕ) (h : k ≤ k) (x : T.carrier k) : downTo T k k h x = x := by
  cases k with
  | zero => rfl
  | succ n => simp [downTo]

theorem upTo_succ (k n : ℕ) (h : k ≤ n) (x : T.carrier k) :
    upTo T k (n + 1) (h.trans (Nat.le_succ n)) x = (T.step n).emb (upTo T k n h x) := by
  have hne : k ≠ n + 1 := by omega
  simp [upTo, hne]

/-- Descending to `n+1` and then projecting is descending to `n`. -/
theorem proj_downTo : ∀ (k n : ℕ) (h : n + 1 ≤ k) (x : T.carrier k),
    (T.step n).proj (downTo T (n + 1) k h x) = downTo T n k (Nat.le_of_succ_le h) x
  | 0, n, h, x => absurd h (by omega)
  | k + 1, n, h, x => by
      by_cases hk : n + 1 = k + 1
      · have hnk : n = k := by omega
        subst hnk
        simp [downTo, downTo_self]
      · have h1 : n + 1 ≤ k := by omega
        have h2 : n ≠ k + 1 := by omega
        simp only [downTo, dif_neg hk, dif_neg h2]
        exact proj_downTo k n h1 ((T.step k).proj x)



/-- The coherent sequence representing `x : T.carrier k`: climb above `k`, descend below it. -/
def embSeq (k : ℕ) (x : T.carrier k) (n : ℕ) : T.carrier n :=
  if h : k ≤ n then upTo T k n h x
  else downTo T n k (Nat.le_of_lt (Nat.lt_of_not_le h)) x

/-- **AND IT IS COHERENT**, which is the whole content: three cases, and the middle one
(`k = n+1`) is where climbing and descending have to agree. -/
theorem embSeq_coherent (k : ℕ) (x : T.carrier k) (n : ℕ) :
    (T.step n).proj (embSeq T k x (n + 1)) = embSeq T k x n := by
  by_cases h : k ≤ n
  · simp only [embSeq, dif_pos h, dif_pos (h.trans (Nat.le_succ n))]
    rw [upTo_succ T k n h x, (T.step n).proj_emb]
  · by_cases h2 : k = n + 1
    · subst h2
      simp only [embSeq, dif_pos (le_refl _), dif_neg h]
      rw [upTo_self]
      simp [downTo, downTo_self]
    · have h3 : ¬ (k ≤ n + 1) := by omega
      simp only [embSeq, dif_neg h3, dif_neg h]
      exact proj_downTo T k n (by omega) x

/-- **EACH LEVEL SITS INSIDE THE LIMIT.** -/
def embFun (k : ℕ) (x : T.carrier k) : Limit T := ⟨embSeq T k x, embSeq_coherent T k x⟩

/-- **AND IT IS A SECTION OF THE LIMIT'S OWN PROJECTION** — reading level `k` back off the
sequence returns `x`. This is what makes it an embedding rather than an arbitrary map. -/
theorem proj_embFun (k : ℕ) (x : T.carrier k) : proj T k (embFun T k x) = x := by
  change embSeq T k x k = x
  simp [embSeq, upTo_self]

theorem upTo_mono (k : ℕ) : ∀ n (h : k ≤ n) {x y : T.carrier k}, x ≤ y →
    upTo T k n h x ≤ upTo T k n h y
  | 0, h, x, y, hxy => by
      obtain rfl := Nat.le_zero.1 h; simpa [upTo] using hxy
  | n + 1, h, x, y, hxy => by
      by_cases hk : k = n + 1
      · subst hk; simpa [upTo] using hxy
      · simp only [upTo, dif_neg hk]
        exact (T.step n).emb.monotone (upTo_mono k n _ hxy)

theorem downTo_mono (n : ℕ) : ∀ k (h : n ≤ k) {x y : T.carrier k}, x ≤ y →
    downTo T n k h x ≤ downTo T n k h y
  | 0, h, x, y, hxy => by
      obtain rfl := Nat.le_zero.1 h; simpa [downTo] using hxy
  | k + 1, h, x, y, hxy => by
      by_cases hk : n = k + 1
      · subst hk; simpa [downTo] using hxy
      · simp only [downTo, dif_neg hk]
        exact downTo_mono n k _ ((T.step k).proj.monotone hxy)

theorem embFun_mono (k : ℕ) {x y : T.carrier k} (hxy : x ≤ y) :
    embFun T k x ≤ embFun T k y := by
  intro n
  simp only [embFun, embSeq]
  split
  · exact upTo_mono T k n _ hxy
  · exact downTo_mono T n k _ hxy


/-! ## 6. The embedding is continuous

**The rung §5 named, climbed.** `upTo` and `downTo` are composites of the tower's own continuous
maps together with identity transports along equalities of naturals, so each commutes with `ωSup`;
the two inductions below say so, and `embHom` assembles them.

**§7 CLOSES WHAT THIS SECTION REFUSED TO CLAIM.** The paragraph here read: *"A `→𝒄` is only the
first `EPPair` field. The second, `emb_proj_le`, is **not proved here**. It looks true … but looking
true is what §5 said about continuity, and §5 was writing a cheque. Until it is proved there is no
`EPPair (T.carrier k) (Limit T)` in this file, and none is claimed."* It is proved in §7, by exactly
the two-case argument that paragraph sketched, and `levelPair` is that `EPPair`.
-/

/-- `upTo` bundled as an order homomorphism. -/
def upToHom (k n : ℕ) (h : k ≤ n) : T.carrier k →o T.carrier n :=
  ⟨upTo T k n h, fun _ _ hxy => upTo_mono T k n h hxy⟩

/-- `downTo` bundled as an order homomorphism. -/
def downToHom (n k : ℕ) (h : n ≤ k) : T.carrier k →o T.carrier n :=
  ⟨downTo T n k h, fun _ _ hxy => downTo_mono T n k h hxy⟩

theorem upTo_ωSup (k : ℕ) : ∀ n (h : k ≤ n) (c : Chain (T.carrier k)),
    upTo T k n h (ωSup c) = ωSup (c.map (upToHom T k n h))
  | 0, h, c => by
      obtain rfl := Nat.le_zero.1 h
      simp [upTo, upToHom, Chain.map]
      rfl
  | n + 1, h, c => by
      by_cases hk : k = n + 1
      · subst hk
        simp [upTo, upToHom, Chain.map]
        rfl
      · have h' : k ≤ n := by omega
        simp only [upTo, dif_neg hk]
        rw [upTo_ωSup k n h' c, (T.step n).emb.ωScottContinuous.map_ωSup]
        congr 1
        apply OrderHom.ext
        funext i
        simp [Chain.map, upToHom, upTo, dif_neg hk]

theorem downTo_ωSup (n : ℕ) : ∀ k (h : n ≤ k) (c : Chain (T.carrier k)),
    downTo T n k h (ωSup c) = ωSup (c.map (downToHom T n k h))
  | 0, h, c => by
      obtain rfl := Nat.le_zero.1 h
      simp [downTo, downToHom, Chain.map]
      rfl
  | k + 1, h, c => by
      by_cases hk : n = k + 1
      · subst hk
        simp [downTo, downToHom, Chain.map]
        rfl
      · have h' : n ≤ k := by omega
        simp only [downTo, dif_neg hk]
        rw [(T.step k).proj.ωScottContinuous.map_ωSup, downTo_ωSup n k h']
        congr 1
        apply OrderHom.ext
        funext i
        simp [Chain.map, downToHom, downTo, dif_neg hk]

/-- **AND THE EMBEDDING IS CONTINUOUS**, so it is a `→𝒄` — the rung §5 named. That is the *first*
of an `EPPair`'s two fields and not by itself an `EPPair`; see the section header. -/
def embHom (k : ℕ) : T.carrier k →𝒄 Limit T where
  toFun := embFun T k
  monotone' _ _ h := embFun_mono T k h
  map_ωSup' c := by
    apply Subtype.ext
    funext n
    change embSeq T k (ωSup c) n = ωSup (Limit.levelChain T _ n)
    by_cases h : k ≤ n
    · simp only [embSeq, dif_pos h]
      rw [upTo_ωSup T k n h c]
      congr 1
      apply OrderHom.ext
      funext i
      change upTo T k n h (c i) = embSeq T k (c i) n
      simp [embSeq, dif_pos h]
    · simp only [embSeq, dif_neg h]
      rw [downTo_ωSup T n k (Nat.le_of_lt (Nat.lt_of_not_le h)) c]
      congr 1
      apply OrderHom.ext
      funext i
      change downTo T n k _ (c i) = embSeq T k (c i) n
      simp [embSeq, dif_neg h]

theorem proj_embHom (k : ℕ) (x : T.carrier k) : proj T k (embHom T k x) = x :=
  proj_embFun T k x

/-! ## 7. Each level is an embedding–projection pair into the limit

**The rung §6 named, and it is the last one this construction needs.** `emb_proj_le` splits on the
same case as everything else here. **Below `k`**, descending inside a coherent sequence just reads
off the lower level — that is what coherence *says* — so the composite is an equality, not an
inequality. **Above `k`**, climbing is `emb` applied repeatedly, and each application is bounded by
the tower's own `emb_proj_le` after coherence rewrites `y.1 n` as `(T.step n).proj (y.1 (n+1))`.

**So `levelPair k : EPPair (T.carrier k) (Limit T)` exists**, and the inverse limit is a genuine
cocone of embedding–projection pairs over the tower.

**A note on this file's estimates, now that there are four of them.** Its header once said the
level-into-limit embedding needed transport along `k + (n − k) = n` and called that unavoidable —
**wrong**, §5. §5 said continuity was expected to go through — **right**, §6. §6 said this looked
true — **right**, here. The one estimate that missed was the pessimistic one, and it cost a day of
the map not existing. That is worth knowing about the next such judgement, and it is not evidence
that the next one will be right.

**§8 CLIMBS THE RUNG THIS SECTION NAMED — AND THE NAMING WAS WRONG IN A WAY WORTH KEEPING.** The
paragraph here read: *"`Bilimit` … **needs one thing beyond this section**: that
`⨆ k, embHom k ∘ proj k` is the **identity** on `Limit T`. Every `EPPair` above is a map between
two objects; the bilimit is a statement about the supremum of a chain of self-maps of one of them,
and nothing in this file constructs that chain, let alone computes its supremum."* The chain and
its supremum are built in §8 and the supremum **is** the identity. But *"needs one thing"* was
false: closing it does not close `Bilimit`, which needs the self-maps of the limit to be
**themselves an inverse limit** of the levels' self-maps, and that is not built. The sentence was
in the paragraph whose whole job is to stop the reader over-reading the section, and it
over-claimed. See §8 for what actually remains.
-/

/-- Descending inside a coherent sequence just reads off the lower level. This is coherence,
iterated: `y.2` is the single-step version and the recursion is the same one that defines
`downTo`. -/
theorem downTo_val (y : Limit T) (n : ℕ) : ∀ k (h : n ≤ k), downTo T n k h (y.1 k) = y.1 n
  | 0, h => by obtain rfl := Nat.le_zero.1 h; rfl
  | k + 1, h => by
      by_cases hk : n = k + 1
      · subst hk; simp [downTo]
      · have h' : n ≤ k := by omega
        simp only [downTo, dif_neg hk]
        rw [y.2 k, downTo_val y n k h']

/-- Climbing inside a coherent sequence only loses information. Each step is the tower's own
`emb_proj_le` once coherence has rewritten the target level as a projection of the one above. -/
theorem upTo_val_le (y : Limit T) (k : ℕ) : ∀ n (h : k ≤ n), upTo T k n h (y.1 k) ≤ y.1 n
  | 0, h => by obtain rfl := Nat.le_zero.1 h; exact le_of_eq rfl
  | n + 1, h => by
      by_cases hk : k = n + 1
      · subst hk; simp [upTo]
      · have h' : k ≤ n := by omega
        simp only [upTo, dif_neg hk]
        calc (T.step n).emb (upTo T k n h' (y.1 k))
            ≤ (T.step n).emb (y.1 n) := (T.step n).emb.monotone (upTo_val_le y k n h')
          _ = (T.step n).emb ((T.step n).proj (y.1 (n + 1))) := by rw [y.2 n]
          _ ≤ y.1 (n + 1) := (T.step n).emb_proj_le _

/-- **THE SECOND `EPPair` FIELD**: going into the limit from level `k` and back out never returns
more than you started with. Below `k` it is an equality and above `k` it is the tower's own
`emb_proj_le`, levelwise. -/
theorem embHom_proj_le (k : ℕ) (y : Limit T) : embHom T k (proj T k y) ≤ y := by
  intro n
  change embSeq T k (y.1 k) n ≤ y.1 n
  by_cases h : k ≤ n
  · simp only [embSeq, dif_pos h]
    exact upTo_val_le T y k n h
  · simp only [embSeq, dif_neg h]
    exact le_of_eq (downTo_val T y n k (Nat.le_of_lt (Nat.lt_of_not_le h)))

/-- **EACH LEVEL SITS IN THE LIMIT AS AN EMBEDDING–PROJECTION PAIR.** Both fields are proved:
`proj_embHom` is exact, `embHom_proj_le` is the inequality. -/
def levelPair (k : ℕ) : EPPair (T.carrier k) (Limit T) where
  emb := embHom T k
  proj := proj T k
  proj_emb := proj_embHom T k
  emb_proj_le := embHom_proj_le T k

/-! ## 8. The round trips exhaust the limit

**Every element of the limit is the supremum of its own finite approximations.** Going into level
`k` and back out gives less than you started with (§7); doing it at higher and higher `k` gives
more and more; and the supremum over all `k` is exactly what you started with. That last point is
where coherence does the work: at level `n`, the approximation through level `k` is *already exact*
for every `k ≥ n`, so the chain is eventually constant at each level and its supremum is forced.

**`upTo_succ_left`** is the one new piece of arithmetic — climbing from `k` is climbing from `k+1`
after one `emb` — and it is what makes the round trips a **chain** rather than an unordered family.

**What this does NOT close, and §7 got this wrong.** §7 said `Bilimit` *"needs one thing beyond
this section"*, naming this supremum. That was an understatement made inside the paragraph whose
purpose is to prevent over-reading, which is the worst place for one. `Bilimit` needs the
continuous **self-maps of the limit** to be themselves the inverse limit of the levels' self-maps —
`(Limit T →𝒄 Limit T) ≃ Limit (funTower T)`, where `funTower T` is the tower
`n ↦ (T.carrier n →𝒄 T.carrier n)` with `EPPair.funPair (T.step n)` as its steps. **That tower is
not constructed anywhere in this estate, and neither is the equivalence.** `ωSup_roundTripChain` is
the standard *first* lemma of that argument — it is what lets a self-map be recovered from its
level approximations — and it is one lemma, not the theorem. Two further steps sit after it: the
equivalence just named, and then, for the canonical tower specifically, that shifting a tower by
one level does not change its limit. `CanonicalTower.Bilimit` remains unproved and neither section
here is evidence for it.
-/

/-- Climbing from `k` is climbing from `k+1` after one `emb`. The lemma that makes the round trips
increase with `k`. -/
theorem upTo_succ_left (k : ℕ) : ∀ n (h : k + 1 ≤ n) (x : T.carrier k),
    upTo T k n (Nat.le_of_succ_le h) x = upTo T (k + 1) n h ((T.step k).emb x)
  | 0, h, _ => absurd h (by omega)
  | n + 1, h, x => by
      by_cases hk : k + 1 = n + 1
      · have hkn : k = n := by omega
        subst hkn
        simp [upTo, upTo_self]
      · have h' : k + 1 ≤ n := by omega
        have hne : k ≠ n + 1 := by omega
        simp only [upTo, dif_neg hne, dif_neg hk]
        rw [upTo_succ_left k n h' x]

/-- Inside a coherent sequence, climbing to level `n` from a higher starting level gives more. -/
theorem upTo_le_upTo (y : Limit T) {j n : ℕ} (hjn : j ≤ n) {k : ℕ} (hjk : j ≤ k) :
    ∀ (hkn : k ≤ n), upTo T j n hjn (y.1 j) ≤ upTo T k n hkn (y.1 k) := by
  induction k, hjk using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hjk ih =>
      intro hkn
      have hk : k ≤ n := Nat.le_of_succ_le hkn
      calc upTo T j n hjn (y.1 j)
          ≤ upTo T k n hk (y.1 k) := ih hk
        _ = upTo T (k + 1) n hkn ((T.step k).emb (y.1 k)) := upTo_succ_left T k n hkn (y.1 k)
        _ ≤ upTo T (k + 1) n hkn (y.1 (k + 1)) := by
            refine upTo_mono T (k + 1) n hkn ?_
            calc (T.step k).emb (y.1 k)
                = (T.step k).emb ((T.step k).proj (y.1 (k + 1))) := by rw [y.2 k]
              _ ≤ y.1 (k + 1) := (T.step k).emb_proj_le _

/-- The round trips increase with the level: below `n` both sides read off `y` exactly, and above
`n` it is `upTo_le_upTo`. -/
theorem embHom_proj_mono (y : Limit T) {j k : ℕ} (hjk : j ≤ k) :
    embHom T j (proj T j y) ≤ embHom T k (proj T k y) := by
  intro n
  change embSeq T j (y.1 j) n ≤ embSeq T k (y.1 k) n
  by_cases hkn : k ≤ n
  · have hjn : j ≤ n := le_trans hjk hkn
    simp only [embSeq, dif_pos hkn, dif_pos hjn]
    exact upTo_le_upTo T y hjn hjk hkn
  · have hn : n ≤ k := Nat.le_of_lt (Nat.lt_of_not_le hkn)
    simp only [embSeq, dif_neg hkn]
    rw [downTo_val T y n k hn]
    exact (embHom_proj_le T j y) n

/-- The chain of round trips through level `k`, at a fixed point of the limit. -/
def embProjChain (y : Limit T) : Chain (Limit T) :=
  ⟨fun k => embHom T k (proj T k y), fun _ _ h => embHom_proj_mono T y h⟩

@[simp] theorem embProjChain_apply (y : Limit T) (k : ℕ) :
    embProjChain T y k = embHom T k (proj T k y) := rfl

/-- **AND ITS SUPREMUM IS `y` ITSELF.** Upward by §7, since every round trip is `≤ y`; downward
because the `n`-th round trip is already **exact** at level `n`, so `y.1 n` is in the chain. -/
theorem ωSup_embProjChain (y : Limit T) : ωSup (embProjChain T y) = y := by
  apply le_antisymm
  · refine ωSup_le _ _ fun k => ?_
    rw [embProjChain_apply]
    exact embHom_proj_le T k y
  · intro n
    have hn : (embProjChain T y n).1 n = y.1 n := by
      rw [embProjChain_apply]
      change embSeq T n (y.1 n) n = y.1 n
      simp [embSeq, upTo_self]
    calc y.1 n = (embProjChain T y n).1 n := hn.symm
      _ ≤ (ωSup (embProjChain T y)).1 n := (le_ωSup (embProjChain T y) n) n

/-- Into level `k` and back out, as a continuous self-map of the limit. -/
def levelRoundTrip (k : ℕ) : Limit T →𝒄 Limit T := (embHom T k).comp (proj T k)

@[simp] theorem levelRoundTrip_apply (k : ℕ) (y : Limit T) :
    levelRoundTrip T k y = embHom T k (proj T k y) := rfl

/-- The round trips as a chain of **self-maps** of the limit, which is the form the bilimit
argument consumes and the form §7 said this file did not construct. -/
def roundTripChain : Chain (Limit T →𝒄 Limit T) :=
  ⟨fun k => levelRoundTrip T k, fun _ _ h y => embHom_proj_mono T y h⟩

@[simp] theorem roundTripChain_apply (k : ℕ) : roundTripChain T k = levelRoundTrip T k := rfl

/-- **THE SUPREMUM OF THE ROUND TRIPS IS THE IDENTITY ON THE LIMIT.** The bundled form of
`ωSup_embProjChain`: suprema in `Limit T →𝒄 Limit T` are pointwise, and pointwise this is the
previous theorem. -/
theorem ωSup_roundTripChain : ωSup (roundTripChain T) = ContinuousHom.id := by
  apply ContinuousHom.ext
  intro y
  rw [show (ωSup (roundTripChain T)) = ContinuousHom.ωSup (roundTripChain T) from rfl,
    ContinuousHom.ωSup_apply]
  have hc : ((roundTripChain T).map ContinuousHom.toMono).map (OrderHom.apply y)
      = embProjChain T y := by
    apply OrderHom.ext
    funext k
    rfl
  rw [hc]
  exact ωSup_embProjChain T y

end InverseLimitCPO
