import QSB.CoreCheckedWire

/-!
The parameterized Config A lock changes only bytes carried by push opcodes.
Its entire opcode skeleton agrees with the pinned disposable 880-opcode lock.
This narrows a Core-to-Lean case audit but is still a theorem about the Lean
program, not compiled Bitcoin Core execution.
-/
namespace QSB.LockOpcodeInventory
open ByteMachine
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

def skeleton : Op → Op
  | .push _ => .push []
  | op => op

theorem pushed_skeleton (values : List Bytes) :
    ((values.map Op.push).map skeleton) =
      List.replicate values.length (.push []) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simpa only [List.map_cons, List.length_cons, skeleton,
        List.replicate_succ] using congrArg (Op.push [] :: ·) ih

theorem prior_skeleton (pin nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    (DynamicFullSerialized.priorOps pin nonce commitmentAt).map skeleton =
      (DynamicFullSerialized.priorOps
        DynamicFullSerialized.literalPin
        DynamicFullSerialized.literalFirstNonce
        DynamicFullSerialized.literalFirstCommitment).map skeleton := by
  have size (c : Fin 150 → Bytes) :
      (DynamicFinalInit.commitmentPushes c).length = 150 := by
    simpa [DynamicFinalInit.commitmentPushes] using
      DynamicFinalInit.commitmentPool_length c
  simp only [DynamicFullSerialized.priorOps,
    DynamicFullSerialized.pinOps, DynamicFullSerialized.firstDataOps,
    List.map_append, List.map_cons, List.map_nil]
  rw [pushed_skeleton, pushed_skeleton]
  simp [size, skeleton]

theorem data_skeleton (nonce : Bytes)
    (commitmentAt : Fin 150 → Bytes) :
    (DynamicFinalInit.dataOps nonce commitmentAt).map skeleton =
      List.replicate 302 (.push []) := by
  have size :
      (DynamicFinalInit.commitmentPushes commitmentAt ++
        PoolRollInvariant.finalDummyPushes ++ [[], nonce]).length = 302 := by
    simpa [DynamicFinalInit.dataOps] using
      DynamicFinalInit.dataOps_length nonce commitmentAt
  simp only [DynamicFinalInit.dataOps, pushed_skeleton, size]

theorem literal_program :
    DynamicCheckedCertificate.program CoreCheckedWire.literalLock =
      ByteLayout.program := by
  calc
    _ = DynamicWholeSource.fullProgram
          (ByteLayout.program.take 446) PoolRollInvariant.finalNonce
          FinalSignedLoop.generatedCommitmentAt := by
            simp [DynamicCheckedCertificate.program,
              CoreCheckedWire.literalLock,
              DynamicFullSerialized.literal_prior_ops]
    _ = ByteLayout.program := DynamicWholeSource.literal_full_program

/-- Every parameterized lock has exactly the same ordered opcode kinds as
the disposable fixture, including all signature and comparison sites. -/
theorem program_skeleton (lock : DynamicCheckedCertificate.Lock) :
    (DynamicCheckedCertificate.program lock).map skeleton =
      ByteLayout.program.map skeleton := by
  have same :
      (DynamicCheckedCertificate.program lock).map skeleton =
        (DynamicCheckedCertificate.program
          CoreCheckedWire.literalLock).map skeleton := by
    simp only [DynamicCheckedCertificate.program,
      DynamicWholeSource.fullProgram,
      DynamicFinalInit.finalRoundProgram, List.map_append]
    rw [prior_skeleton, data_skeleton]
    simp only [CoreCheckedWire.literalLock]
    rw [data_skeleton]
  simpa [literal_program] using same

structure Counts where
  push : Nat
  dup : Nat
  overOp : Nat
  swap : Nat
  roll : Nat
  min : Nat
  add : Nat
  hash160 : Nat
  sha256 : Nat
  equalverify : Nat
  checksigverify : Nat
  checkmultisig : Nat
  deriving DecidableEq, Repr

/-- Count constructors in a list whose pushes have first been canonicalized
with `skeleton`. -/
def inventory (ops : List Op) : Counts :=
  { push := ops.count (.push [])
    dup := ops.count .dup
    overOp := ops.count .over
    swap := ops.count .swap
    roll := ops.count .roll
    min := ops.count .min
    add := ops.count .add
    hash160 := ops.count .hash160
    sha256 := ops.count .sha256
    equalverify := ops.count .equalverify
    checksigverify := ops.count .checksigverify
    checkmultisig := ops.count .checkmultisig }

theorem literal_inventory :
    inventory (ByteLayout.program.map skeleton) =
      { push := 699, dup := 17, overOp := 1, swap := 1,
        roll := 90, min := 18, add := 15, hash160 := 15,
        sha256 := 3, equalverify := 15, checksigverify := 4,
        checkmultisig := 2 } := by decide

/-- The same twelve-case inventory holds for every parameterized Config A
lock, independent of the values of all three fixed signatures and both
commitment pools. -/
theorem program_inventory (lock : DynamicCheckedCertificate.Lock) :
    inventory ((DynamicCheckedCertificate.program lock).map skeleton) =
      { push := 699, dup := 17, overOp := 1, swap := 1,
        roll := 90, min := 18, add := 15, hash160 := 15,
        sha256 := 3, equalverify := 15, checksigverify := 4,
        checkmultisig := 2 } := by
  rw [program_skeleton]
  exact literal_inventory

def counted : Op → Nat
  | .push _ => 0
  | _ => 1

theorem counted_skeleton (op : Op) : counted (skeleton op) = counted op := by
  cases op <;> rfl

theorem literal_counted_ops :
    (ByteLayout.program.map counted).sum = 181 := by decide

/-- The ordinary above-OP_16 opcode count is 181 for every parameterized
Config A lock. Core additionally charges reached CHECKMULTISIG key counts. -/
theorem program_counted_ops (lock : DynamicCheckedCertificate.Lock) :
    ((DynamicCheckedCertificate.program lock).map counted).sum = 181 := by
  have same := congrArg
    (fun ops : List Op => (ops.map counted).sum)
    (program_skeleton lock)
  simpa [List.map_map, counted_skeleton, literal_counted_ops] using same

end QSB.LockOpcodeInventory
