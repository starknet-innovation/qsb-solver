import QSB.PoolRollInvariant

/-!
The exact source positions for the first signed selection of the generated
second round, after its commitment/dummy/zero/nonce pushes. These are local
stack facts. Connecting every accepted comparison to this source map remains
the byte-execution invariant to prove.
-/
namespace QSB.FinalSignedBoundary
open ByteMachine
open PoolRollInvariant
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

def finalCommitmentPushOps : List Op := ByteLayout.program.drop 447 |>.take 150

def finalCommitmentPushes : List Bytes :=
  finalCommitmentPushOps.filterMap FirstOvershoot.pushValue

def finalCommitmentPool : List Bytes := finalCommitmentPushes.reverse

theorem generated_commitment_ops_are_pushes :
    finalCommitmentPushOps = finalCommitmentPushes.map Op.push := by decide

theorem generated_commitment_pool_length :
    finalCommitmentPool.length = 150 := by decide

theorem generated_commitment_pool_width :
    ∀ x ∈ finalCommitmentPool, x.length = 20 := by
  have checked : List.Forall (fun x => x.length = 20)
      finalCommitmentPool := by decide
  exact List.forall_iff_forall_mem.mp checked

theorem generated_dummy_pool_width :
    ∀ x ∈ finalDummyPool, x.length = 9 := by
  have checked : List.Forall (fun x => x.length = 9)
      finalDummyPool := by decide
  exact List.forall_iff_forall_mem.mp checked

def lookupRegion (retained prior : Bytes) (tail : List Bytes) : List Bytes :=
  retained :: finalNonce :: [] ::
    (finalDummyPool ++ finalCommitmentPool ++ prior :: tail)

/-- The two lowest numeric choices pick a generated 9-byte dummy signature,
which cannot equal a 20-byte HASH160 output. -/
theorem low_index_source_is_dummy (retained prior : Bytes)
    (tail : List Bytes) (n : Nat) (hn : n < 2) :
    ∃ chosen : Bytes,
      (lookupRegion retained prior tail)[151 + n]? = some chosen ∧
      chosen.length = 9 := by
  have hj : 148 + n < finalDummyPool.length := by
    rw [generated_dummy_pool_length]
    omega
  let chosen := finalDummyPool[148 + n]
  have source : (lookupRegion retained prior tail)[151 + n]? =
      some chosen := by
    change ([retained, finalNonce, []] ++
      (finalDummyPool ++ finalCommitmentPool ++ prior :: tail))[151 + n]? =
      some chosen
    rw [List.getElem?_append_right (by simp; omega)]
    have frontLen : ([retained, finalNonce, []] : List Bytes).length = 3 := by
      simp
    rw [frontLen]
    have index : 151 + n - 3 = 148 + n := by omega
    rw [index]
    rw [List.append_assoc]
    rw [List.getElem?_append_left hj]
    exact List.getElem?_eq_getElem hj
  have width : chosen.length = 9 :=
    generated_dummy_pool_width chosen (List.getElem_mem hj)
  exact ⟨chosen, source, width⟩

/-- Numeric choices 2 through 151 name one of the 150 generated 20-byte
commitments, indexed by `n-2`, independent of the earlier stack. -/
theorem middle_index_source_is_commitment (retained prior : Bytes)
    (tail : List Bytes) (n : Nat) (low : 2 ≤ n) (high : n < 152) :
    (lookupRegion retained prior tail)[151 + n]? =
      finalCommitmentPool[n - 2]? := by
  have idx : n - 2 < finalCommitmentPool.length := by
    rw [generated_commitment_pool_length]
    omega
  change (([retained, finalNonce, []] ++ finalDummyPool) ++
    (finalCommitmentPool ++ prior :: tail))[151 + n]? =
    finalCommitmentPool[n - 2]?
  have frontLen : ([retained, finalNonce, []] ++ finalDummyPool).length =
      153 := by simp [generated_dummy_pool_length]
  rw [List.getElem?_append_right (by rw [frontLen]; omega)]
  have index : 151 + n - ([retained, finalNonce, []] ++
      finalDummyPool).length = n - 2 := by rw [frontLen]; omega
  rw [index]
  exact List.getElem?_append_left idx

theorem low_index_cannot_match_hash160 (hashes : Hashes)
    (opening retained prior : Bytes) (tail : List Bytes)
    (n : Nat) (hn : n < 2) :
    hashes.h160 opening ≠
      (lookupRegion retained prior tail)[151 + n]?.getD [] := by
  obtain ⟨chosen, source, width⟩ :=
    low_index_source_is_dummy retained prior tail n hn
  rw [source]
  simp only [Option.getD_some]
  intro equal
  have hashWidth := hashes.h160_width opening
  rw [equal] at hashWidth
  omega

/-- The capped value 152 reaches the previous round's CHECKMULTISIG result,
not any second-round HORS commitment or dummy signature. -/
theorem cap_source_is_prior_result (retained prior : Bytes)
    (tail : List Bytes) :
    (lookupRegion retained prior tail)[303]? = some prior := by
  simp [lookupRegion, List.getElem?_append,
    generated_dummy_pool_length, generated_commitment_pool_length]

theorem cap_roll_moves_prior_result (retained prior : Bytes)
    (tail : List Bytes) :
    KeyRolls.rollAt 303 (lookupRegion retained prior tail) =
      some (prior :: retained :: finalNonce :: [] ::
        (finalDummyPool ++ finalCommitmentPool ++ tail)) := by
  have frontLength :
      (retained :: finalNonce :: [] ::
        (finalDummyPool ++ finalCommitmentPool)).length = 303 := by
    simp [generated_dummy_pool_length, generated_commitment_pool_length]
  have rolled := PoolRollInvariant.roll_from_middle
    (retained :: finalNonce :: [] ::
      (finalDummyPool ++ finalCommitmentPool)) [prior] tail 0 (by simp)
  simpa [lookupRegion, frontLength, List.append_assoc] using rolled

theorem cap_source_cannot_match_hash160 (hashes : Hashes)
    (opening retained prior : Bytes) (tail : List Bytes)
    (priorShort : prior.length ≤ 1) :
    hashes.h160 opening ≠
      (lookupRegion retained prior tail)[303]?.getD [] := by
  rw [cap_source_is_prior_result]
  simp only [Option.getD_some]
  intro equal
  have width := hashes.h160_width opening
  rw [equal] at width
  omega

theorem cap_cannot_match_prior_multisig_result (hashes : Hashes)
    (opening retained : Bytes) (tail : List Bytes) (result : Bool) :
    hashes.h160 opening ≠
      (lookupRegion retained (ByteMachine.boolBytes result) tail)[303]?.getD [] := by
  apply cap_source_cannot_match_hash160
  cases result <;> decide

theorem generated_first_signed_comparison_tail :
    (ByteLayout.program.drop 756).take 5 =
      [.roll, .push [0x53, 0x02], .roll,
        .hash160, .equalverify] := by decide

theorem capped_offset_encoding :
    ByteIndex.parseScriptNum [0x98, 0x00] = some 152 ∧
    ByteIndex.parseScriptNum [0x97, 0x00] = some 151 ∧
    ByteIndex.encodeScriptNum (152 + 151) = some [0x2f, 0x01] := by
  decide

theorem preimage_roll_index_decode :
    ByteIndex.parseScriptNum [0x53, 0x02] = some 595 := by decide

/-- The generated deep preimage roll shifts the existing comparison target
from top to depth one. A target shorter than 20 bytes cannot then pass the
HASH160 comparison, regardless of the supplied opening. -/
theorem short_target_rejects_comparison (hashes : Hashes)
    (target : Bytes) (rest : List Bytes) (outcomes : List Bool)
    (cost : Nat) (final : State) (short : target.length < 20)
    (accepted : run hashes
      [.push [0x53, 0x02], .roll, .hash160, .equalverify]
      (State.mk (target :: rest) outcomes cost) = some final) : False := by
  have split : ([.push [0x53, 0x02], .roll,
      .hash160, .equalverify] : List Op) =
      [.push [0x53, 0x02], .roll] ++ [.hash160, .equalverify] := rfl
  rw [split, run_append] at accepted
  cases first : run hashes [.push [0x53, 0x02], .roll]
      (State.mk (target :: rest) outcomes cost) with
  | none => simp [first] at accepted
  | some middle =>
      have preserved := ByteFinalCounts.accepted_pair_preserves_shallower_option
        hashes [0x53, 0x02] 595 0 (target :: rest) outcomes cost middle
        preimage_roll_index_decode (by omega) first
      simp only [first, Option.bind_some] at accepted
      cases middle with
      | mk middleStack middleOutcomes middleCost =>
          cases middleStack with
          | nil => simp at preserved
          | cons opening below =>
              cases below with
              | nil => simp at preserved
              | cons compared tail =>
                  have same : compared = target := by
                    simpa using preserved
                  subst compared
                  have equalHash := ByteMachine.successful_hash_comparison
                    hashes opening target tail middleOutcomes middleCost []
                    (by rw [accepted]; rfl)
                  have width := hashes.h160_width opening
                  rw [equalHash] at width
                  omega

/-- The first final-round signed selection cannot use numeric raw index 0
or 1: its signed roll selects a generated nine-byte dummy, which fails the
HASH160 comparison. The earlier stack tail and the raw offset encoding are
arbitrary. -/
theorem low_first_signed_comparison_rejects (hashes : Hashes)
    (offset retained prior : Bytes) (tail : List Bytes)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (n : Nat) (low : n < 2)
    (parsed : ByteIndex.parseScriptNum offset = some (Int.ofNat (151 + n)))
    (accepted : run hashes ((ByteLayout.program.drop 756).take 5)
      (State.mk (offset :: lookupRegion retained prior tail)
        outcomes cost) = some final) : False := by
  rw [generated_first_signed_comparison_tail] at accepted
  obtain ⟨afterRoll, rolled, _, suffix⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push [0x53, 0x02], .roll, .hash160, .equalverify]
      (State.mk (offset :: lookupRegion retained prior tail)
        outcomes cost) final accepted
  have budget := ByteFinalCounts.roll_success_budget hashes offset
    (lookupRegion retained prior tail) outcomes cost afterRoll rolled
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes offset
    (151 + n) (lookupRegion retained prior tail)
    outcomes cost parsed budget] at rolled
  obtain ⟨chosen, source, width⟩ :=
    low_index_source_is_dummy retained prior tail n low
  unfold KeyRolls.rollAt at rolled
  rw [source] at rolled
  simp at rolled
  cases rolled
  exact short_target_rejects_comparison hashes chosen
    ((lookupRegion retained prior tail).eraseIdx (151 + n))
    outcomes (cost + 1) final (by omega) suffix

/-- With the exact five-opcode generated tail, a capped first signed choice
of 152 cannot pass the HORS comparison when the prior round left its ordinary
Boolean CHECKMULTISIG result. This is local to the stated post-ADD stack. -/
theorem capped_first_signed_comparison_rejects (hashes : Hashes)
    (retained : Bytes) (tail : List Bytes) (result : Bool)
    (outcomes : List Bool) (cost : Nat) (final : State)
    (accepted : run hashes ((ByteLayout.program.drop 756).take 5)
      (State.mk ([0x2f, 0x01] ::
        lookupRegion retained (ByteMachine.boolBytes result) tail)
        outcomes cost) = some final) : False := by
  rw [generated_first_signed_comparison_tail] at accepted
  obtain ⟨afterRoll, rolled, _, suffix⟩ :=
    FirstAcceptedOrigin.run_cons_success hashes .roll
      [.push [0x53, 0x02], .roll, .hash160, .equalverify]
      (State.mk ([0x2f, 0x01] ::
        lookupRegion retained (ByteMachine.boolBytes result) tail)
        outcomes cost) final accepted
  have budget := ByteFinalCounts.roll_success_budget hashes [0x2f, 0x01]
    (lookupRegion retained (ByteMachine.boolBytes result) tail)
    outcomes cost afterRoll rolled
  have decoded : ByteIndex.parseScriptNum [0x2f, 0x01] = some 303 := by
    decide
  rw [FirstOvershoot.byte_roll_matches_list_roll hashes [0x2f, 0x01]
    303 (lookupRegion retained (ByteMachine.boolBytes result) tail)
    outcomes cost decoded budget] at rolled
  rw [cap_roll_moves_prior_result] at rolled
  cases rolled
  exact short_target_rejects_comparison hashes
    (ByteMachine.boolBytes result)
    (retained :: finalNonce :: [] ::
      (finalDummyPool ++ finalCommitmentPool ++ tail))
    outcomes (cost + 1) final
    (by cases result <;> decide) suffix

end QSB.FinalSignedBoundary
