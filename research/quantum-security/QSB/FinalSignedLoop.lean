import QSB.FinalSignedAccepted

/-!
Structural invariant for the seven generated final-round signed selections.
The first selection's accepted-run origin is established in
`FinalSignedAccepted`; this module identifies the shared stack geometry that
must be preserved when lifting the remaining six selections.
-/
namespace QSB.FinalSignedLoop
open ByteMachine
open PoolRollInvariant
open FinalSignedBoundary
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def signedRoundOps (k : Fin 7) : List Op :=
  ByteLayout.program.drop (751 + 13 * k.val) |>.take 11

def signedGap (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (151 - k.val))).getD []

def preimageIndex (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (595 - 2 * k.val))).getD []

/-- All seven literal signed-selection blocks share the same MIN/ADD,
commitment-roll, preimage-roll, comparison, and dummy-roll pattern. -/
theorem generated_signed_round_ops :
    ∀ k : Fin 7, signedRoundOps k =
      [.push [0x98, 0x00], .min, .dup, .push (signedGap k), .add,
       .roll, .push (preimageIndex k), .roll, .hash160,
       .equalverify, .roll] := by decide

def fixedRawIndex (k : Fin 7) : Bytes :=
  (ByteIndex.encodeScriptNum (Int.ofNat (586 - k.val))).getD []

theorem generated_fixed_raw_index_pairs :
    ∀ k : Fin 7,
      (ByteLayout.program.drop (749 + 13 * k.val)).take 2 =
        [.push (fixedRawIndex k), .roll] := by decide

theorem generated_signed_gap_decodes :
    ∀ k : Fin 7,
      ByteIndex.parseScriptNum (signedGap k) =
        some (Int.ofNat (151 - k.val)) := by decide

theorem generated_preimage_index_decodes :
    ∀ k : Fin 7,
      ByteIndex.parseScriptNum (preimageIndex k) =
        some (Int.ofNat (595 - 2 * k.val)) := by decide

structure PoolShape (gathered dummies commitments : List Bytes) : Prop where
  poolCount : gathered.length + dummies.length = 150
  commitmentCount : commitments.length = dummies.length
  gatheredWidth : ∀ x ∈ gathered, x.length = 9
  dummyWidth : ∀ x ∈ dummies, x.length = 9
  commitmentWidth : ∀ x ∈ commitments, x.length = 20

def generatedDummyAt (i : Fin 150) : Bytes :=
  finalDummyPool[i.val]'(by
    rw [generated_dummy_pool_length]
    exact i.isLt)

def generatedCommitmentAt (i : Fin 150) : Bytes :=
  finalCommitmentPool[i.val]'(by
    rw [generated_commitment_pool_length]
    exact i.isLt)

/-- A common surviving original-position list records that the dummy and
commitment pools have undergone exactly the same prior erasures. -/
structure AlignedPool (ids : List (Fin 150))
    (dummies commitments : List Bytes) : Prop where
  dummyMap : dummies = ids.map generatedDummyAt
  commitmentMap : commitments = ids.map generatedCommitmentAt

theorem generated_initial_pool_alignment :
    AlignedPool (List.finRange 150) finalDummyPool finalCommitmentPool := by
  constructor <;> decide

theorem paired_erasure_preserves_alignment
    (ids : List (Fin 150)) (dummies commitments : List Bytes)
    (aligned : AlignedPool ids dummies commitments) (j : Nat) :
    AlignedPool (ids.eraseIdx j)
      (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.eraseIdx_map]
  · rw [commitmentMap, List.eraseIdx_map]

theorem aligned_pair_at (ids : List (Fin 150))
    (dummies commitments : List Bytes)
    (aligned : AlignedPool ids dummies commitments)
    (j : Nat) (within : j < ids.length) :
    dummies[j]? = some (generatedDummyAt ids[j]) ∧
    commitments[j]? = some (generatedCommitmentAt ids[j]) := by
  rcases aligned with ⟨dummyMap, commitmentMap⟩
  constructor
  · rw [dummyMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl
  · rw [commitmentMap, List.getElem?_map,
      List.getElem?_eq_getElem within]
    rfl

theorem generated_initial_pool_shape :
    PoolShape [] finalDummyPool finalCommitmentPool := by
  refine ⟨?_, ?_, ?_, generated_dummy_pool_width,
    generated_commitment_pool_width⟩
  · simpa using generated_dummy_pool_length
  · rw [generated_commitment_pool_length, generated_dummy_pool_length]
  · simp

/-- A paired commitment and dummy draw at the same current pool position
preserves the widths and count equation for the next signed selection. -/
theorem paired_draw_preserves_pool_shape
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < dummies.length) :
    PoolShape (dummies[j] :: gathered)
      (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  have commitmentWithin : j < commitments.length := by
    rw [shape.commitmentCount]
    exact within
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_eraseIdx, if_pos within]
    have count := shape.poolCount
    omega
  · simp only [List.length_eraseIdx, if_pos within,
      if_pos commitmentWithin]
    rw [shape.commitmentCount]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | old
    · exact shape.dummyWidth dummies[j] (List.getElem_mem within)
    · exact shape.gatheredWidth x old
  · intro x hx
    exact shape.dummyWidth x (List.mem_of_mem_eraseIdx hx)
  · intro x hx
    exact shape.commitmentWidth x (List.mem_of_mem_eraseIdx hx)

def signedPrefix (retained : Bytes) (gathered dummies : List Bytes) :
    List Bytes :=
  [retained] ++ gathered ++ [finalNonce, []] ++ dummies

def signedRegion (retained : Bytes) (gathered dummies commitments : List Bytes)
    (prior : Bytes) (tail : List Bytes) : List Bytes :=
  signedPrefix retained gathered dummies ++ (commitments ++ prior :: tail)

def preimageFront (selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes) (j : Nat) : List Bytes :=
  [selected] ++ signedPrefix retained gathered dummies ++
    commitments.eraseIdx j ++ [prior]

def nextRawFront (prior : Bytes)
    (gathered dummies commitments : List Bytes) : List Bytes :=
  gathered ++ [finalNonce, []] ++ dummies ++ commitments ++ [prior]

/-- Once each prior signed selection has removed one dummy, the commitment
pool always begins at absolute depth 153 after the newly retained index. -/
theorem signed_prefix_length (retained : Bytes)
    (gathered dummies : List Bytes)
    (poolLength : gathered.length + dummies.length = 150) :
    (signedPrefix retained gathered dummies).length = 153 := by
  simp [signedPrefix]
  omega

theorem signed_prefix_wrong_width (retained : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4) :
    ∀ x ∈ signedPrefix retained gathered dummies, x.length ≠ 20 := by
  intro x hx
  simp only [signedPrefix, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with hfront | dummyHit
  · rcases hfront with hbefore | hnonceOrZero
    · rcases hbefore with hretained | gatheredHit
      · subst x
        omega
      · have width := shape.gatheredWidth x gatheredHit
        omega
    · rcases hnonceOrZero with hnonce | hzero
      · subst x
        decide
      · subst x
        decide
  · have width := shape.dummyWidth x dummyHit
    omega

/-- Every source before the commitment window has non-HASH160 width,
including any previously gathered nine-byte dummy signatures. -/
theorem shallow_signed_source_wrong_width (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (retainedSmall : retained.length ≤ 4)
    (n : Nat) (shallow : n < 153) :
    ∃ chosen : Bytes,
      (signedRegion retained gathered dummies commitments prior tail)[n]? =
        some chosen ∧ chosen.length ≠ 20 := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  have within : n < (signedPrefix retained gathered dummies).length := by
    rw [prefixLength]
    exact shallow
  let chosen := (signedPrefix retained gathered dummies)[n]
  have source :
      (signedRegion retained gathered dummies commitments prior tail)[n]? =
        some chosen := by
    unfold signedRegion
    rw [List.getElem?_append_left within]
    exact List.getElem?_eq_getElem within
  exact ⟨chosen, source,
    signed_prefix_wrong_width retained gathered dummies commitments
      shape retainedSmall chosen (List.getElem_mem within)⟩

theorem signed_commitment_source (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolLength : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    (signedRegion retained gathered dummies commitments prior tail)[153 + j]? =
      commitments[j]? := by
  unfold signedRegion
  rw [List.getElem?_append_right (by
    rw [signed_prefix_length retained gathered dummies poolLength]
    omega)]
  have index : 153 + j -
      (signedPrefix retained gathered dummies).length = j := by
    rw [signed_prefix_length retained gathered dummies poolLength]
    omega
  rw [index]
  exact List.getElem?_append_left within

/-- Clamping a signed index to 152 selects the previous round's Boolean
result at the end of the current commitment pool. -/
theorem capped_signed_source_is_prior (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (signedRegion retained gathered dummies commitments prior tail)[303 -
      gathered.length]? = some prior := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  have frontLength :
      (signedPrefix retained gathered dummies ++ commitments).length =
        303 - gathered.length := by
    simp only [List.length_append]
    rw [prefixLength, shape.commitmentCount]
    have count := shape.poolCount
    omega
  unfold signedRegion
  rw [← List.append_assoc]
  rw [List.getElem?_append_right (by rw [frontLength])]
  rw [frontLength]
  simp

/-- The commitment roll removes precisely one current commitment while
preserving the gathered signatures, nonce, zero dummy, and remaining dummies. -/
theorem commitment_roll_shape (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (poolLength : gathered.length + dummies.length = 150)
    (j : Nat) (within : j < commitments.length) :
    KeyRolls.rollAt (153 + j)
      (signedRegion retained gathered dummies commitments prior tail) =
      some (commitments[j] ::
        signedPrefix retained gathered dummies ++
        commitments.eraseIdx j ++ prior :: tail) := by
  have moved := PoolRollInvariant.roll_from_middle
    (signedPrefix retained gathered dummies) commitments
    (prior :: tail) j within
  simpa [signedRegion,
    signed_prefix_length retained gathered dummies poolLength,
    List.append_assoc] using moved

/-- The following raw-index roll uses the same current pool position `j` to
move its nine-byte dummy signature above the previously gathered signatures.
This is the exact paired-roll transition needed by the seven-round invariant. -/
theorem paired_dummy_roll_shape (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (j : Nat) (within : j < dummies.length) :
    KeyRolls.rollAt (gathered.length + 2 + j)
      (gathered ++ [finalNonce, []] ++ dummies ++
        commitments ++ prior :: tail) =
      some (dummies[j] :: gathered ++ [finalNonce, []] ++
        dummies.eraseIdx j ++ commitments ++ prior :: tail) := by
  simpa [List.append_assoc] using
    (PoolRollInvariant.roll_at_pool gathered dummies
      (commitments ++ prior :: tail) finalNonce j within)

theorem preimage_front_length (selected retained prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length) :
    (preimageFront selected retained prior gathered dummies commitments j).length =
      304 - gathered.length := by
  have prefixLength := signed_prefix_length retained gathered dummies
    shape.poolCount
  simp only [preimageFront, List.length_append, List.length_cons,
    List.length_nil, List.length_eraseIdx, if_pos within]
  rw [prefixLength, shape.commitmentCount]
  have count := shape.poolCount
  have positive : 0 < dummies.length := by
    rw [shape.commitmentCount] at within
    omega
  omega

/-- In each pool-shaped round, the generated deep preimage roll reaches the
earlier tail at offset `291-k`, with `k` already gathered signatures. -/
theorem preimage_roll_tail_source (selected retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (j : Nat) (within : j < commitments.length)
    (enough : 291 - gathered.length < tail.length) :
    KeyRolls.rollAt (595 - 2 * gathered.length)
      (preimageFront selected retained prior gathered dummies commitments j ++
        tail) =
      some (tail[291 - gathered.length] ::
        preimageFront selected retained prior gathered dummies commitments j ++
        tail.eraseIdx (291 - gathered.length)) := by
  have frontLength := preimage_front_length selected retained prior
    gathered dummies commitments shape j within
  have depth :
      (preimageFront selected retained prior gathered dummies commitments j).length +
        (291 - gathered.length) = 595 - 2 * gathered.length := by
    rw [frontLength]
    have count := shape.poolCount
    omega
  have moved := PoolRollInvariant.roll_from_middle
    (preimageFront selected retained prior gathered dummies commitments j)
    tail [] (291 - gathered.length) enough
  simpa [depth] using moved

theorem next_raw_front_length (prior : Bytes)
    (gathered dummies commitments : List Bytes)
    (shape : PoolShape gathered dummies commitments) :
    (nextRawFront prior gathered dummies commitments).length =
      303 - gathered.length := by
  simp only [nextRawFront, List.length_append, List.length_cons,
    List.length_nil]
  rw [shape.commitmentCount]
  have count := shape.poolCount
  omega

/-- Every generated fixed raw-index roll after a pool-shaped draw fetches
tail cell 283, despite the changing encoded roll depth. -/
theorem fixed_raw_roll_tail_source (prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (enough : 283 < tail.length) :
    KeyRolls.rollAt (586 - gathered.length)
      (nextRawFront prior gathered dummies commitments ++ tail) =
      some (tail[283] ::
        nextRawFront prior gathered dummies commitments ++
        tail.eraseIdx 283) := by
  have frontLength := next_raw_front_length prior gathered dummies
    commitments shape
  have depth :
      (nextRawFront prior gathered dummies commitments).length + 283 =
        586 - gathered.length := by
    rw [frontLength]
    have count := shape.poolCount
    omega
  have moved := PoolRollInvariant.roll_from_middle
    (nextRawFront prior gathered dummies commitments) tail [] 283 enough
  simpa [depth] using moved

/-- For any in-range raw index above the current shallow boundary, the
generated signed offset reaches commitment `j`; the later raw-index roll
reaches dummy `j`. Their paired removals preserve the pool invariant. -/
theorem inrange_paired_roll_transition (retained prior : Bytes)
    (gathered dummies commitments tail : List Bytes)
    (shape : PoolShape gathered dummies commitments)
    (n : Fin 152) (low : gathered.length + 2 ≤ n.val) :
    ∃ (j : Nat) (dummyWithin : j < dummies.length)
      (commitmentWithin : j < commitments.length),
      n.val = gathered.length + 2 + j ∧
      KeyRolls.rollAt (151 - gathered.length + n.val)
        (signedRegion retained gathered dummies commitments prior tail) =
        some (commitments[j]'commitmentWithin ::
          signedPrefix retained gathered dummies ++
          commitments.eraseIdx j ++ prior :: tail) ∧
      KeyRolls.rollAt n.val
        (gathered ++ [finalNonce, []] ++ dummies ++
          commitments.eraseIdx j ++ prior :: tail) =
        some (dummies[j]'dummyWithin :: gathered ++ [finalNonce, []] ++
          dummies.eraseIdx j ++ commitments.eraseIdx j ++ prior :: tail) ∧
      PoolShape (dummies[j]'dummyWithin :: gathered)
        (dummies.eraseIdx j) (commitments.eraseIdx j) := by
  let j := n.val - (gathered.length + 2)
  have within : j < dummies.length := by
    have count := shape.poolCount
    dsimp [j]
    omega
  have commitmentWithin : j < commitments.length := by
    rw [shape.commitmentCount]
    exact within
  have rawEq : n.val = gathered.length + 2 + j := by
    dsimp [j]
    omega
  have signedEq : 151 - gathered.length + n.val = 153 + j := by
    have count := shape.poolCount
    dsimp [j]
    omega
  refine ⟨j, within, commitmentWithin, rawEq, ?_, ?_,
    paired_draw_preserves_pool_shape gathered dummies commitments
      shape j within⟩
  · rw [signedEq]
    exact commitment_roll_shape retained prior gathered dummies
      commitments tail shape.poolCount j commitmentWithin
  · rw [rawEq]
    exact paired_dummy_roll_shape prior gathered dummies
      (commitments.eraseIdx j) tail j within

end QSB.FinalSignedLoop
