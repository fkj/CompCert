(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

Require Import String.
Require Import Coqlib.
Require Import Decidableplus.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.
  These are integer registers that can be allocated to RTL pseudo-registers ([Rxx]).

  The type [mreg] does not include reserved machine registers such as
  the zero register (r0), the frame pointer (r30), and the stack pointer (r31).
  It also does not include special registers and predicate registers.
  Finally, register r29 is reserved for use as a temporary by the
  assembly-code generator [Asmgen].
*)

Inductive mreg: Type :=
 (** Allocatable integer regs. *)
              | R1:  mreg | R2:  mreg | R3:  mreg
  | R4:  mreg | R5:  mreg | R6:  mreg | R7:  mreg
  | R8:  mreg | R9:  mreg | R10: mreg | R11: mreg
  | R12: mreg | R13: mreg | R14: mreg | R15: mreg
  | R16: mreg | R17: mreg | R18: mreg | R19: mreg
  | R20: mreg | R21: mreg | R22: mreg | R23: mreg
  | R24: mreg | R25: mreg | R26: mreg | R27: mreg
  | R28: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition all_mregs :=
    R1 :: R2 :: R3 :: R4 :: R5 :: R6 :: R7 :: R8 :: R9
 :: R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17
 :: R18 :: R19 :: R20 :: R21 :: R22 :: R23 :: R24 :: R25
 :: R26 :: R27 :: R28
 :: nil.

Lemma all_mregs_complete:
  forall (r: mreg), In r all_mregs.
Proof.
  assert (forall r, proj_sumbool (In_dec mreg_eq r all_mregs) = true) by (destruct r; reflexivity).
  intros. specialize (H r). InvBooleans. auto.
Qed.

Instance Decidable_eq_mreg : forall (x y: mreg), Decidable (eq x y) := Decidable_eq mreg_eq.
  
Instance Finite_mreg : Finite mreg := {
  Finite_elements := all_mregs;
  Finite_elements_spec := all_mregs_complete
}.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R1  | R2  | R3  | R4  | R5  | R6  | R7
  | R8  | R9  | R10 | R11 | R12 | R13 | R14
  | R15 | R16 | R17 | R18 | R19 | R20 | R21
  | R22 | R23 | R24 | R25 | R26 | R27 | R28 => if Archi.ptr64 then Tany64 else Tany32
  end.

Open Scope positive_scope.

Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R1  =>  1 | R2  =>  2 | R3  =>  3 | R4  =>  4
    | R5  =>  5 | R6  =>  6 | R7  =>  7 | R8  =>  8
    | R9  =>  9 | R10 => 10 | R11 => 11 | R12 => 12
    | R13 => 13 | R14 => 14 | R15 => 15 | R16 => 16
    | R17 => 17 | R18 => 18 | R19 => 19 | R20 => 20
    | R21 => 21 | R22 => 22 | R23 => 23 | R24 => 24
    | R25 => 25 | R26 => 26 | R27 => 27 | R28 => 28
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    decide_goal.
  Qed.
End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Names of registers *)

Local Open Scope string_scope.

Definition register_names :=
  ("R1",  R1)  :: ("R2",  R2)  :: ("R3",  R3)  :: ("R4",  R4)  ::
  ("R5",  R5)  :: ("R6",  R6)  :: ("R7",  R7)  :: ("R8",  R8)  ::
  ("R9",  R9)  :: ("R10", R10) :: ("R11", R11) :: ("R12", R12) ::
  ("R13", R13) :: ("R14", R14) :: ("R15", R15) :: ("R16", R16) ::
  ("R17", R17) :: ("R18", R18) :: ("R19", R19) :: ("R20", R20) ::
  ("R21", R21) :: ("R22", R22) :: ("R23", R23) :: ("R24", R24) ::
  ("R25", R25) :: ("R26", R26) :: ("R27", R27) :: ("R28", R28) :: nil.

Definition register_by_name (s: string) : option mreg :=
  let fix assoc (l: list (string * mreg)) : option mreg :=
    match l with
    | nil => None
    | (s1, r1) :: l' => if string_dec s s1 then Some r1 else assoc l'
    end
  in assoc register_names.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg := nil.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg := nil.

Definition destroyed_by_cond (cond: condition): list mreg := nil.

Definition destroyed_by_jumptable: list mreg := R5 :: nil.

Fixpoint destroyed_by_clobber (cl: list string): list mreg :=
  match cl with
  | nil => nil
  | c1 :: cl =>
      match register_by_name c1 with
      | Some r => r :: destroyed_by_clobber cl
      | None   => destroyed_by_clobber cl
      end
  end.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_inline_asm txt sg clob => destroyed_by_clobber clob
  | EF_memcpy sz al => R5 :: R6 :: R7 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg := nil.

Definition destroyed_at_function_entry: list mreg :=  nil.

Definition temp_for_parent_frame: mreg := R28.

Definition destroyed_at_indirect_call: list mreg :=
  R10 :: R11 :: R12 :: R13 :: R14 :: R15 :: R16 :: R17 :: nil.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg := (nil, None).

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_builtin name sg =>
      if (negb Archi.ptr64) && string_dec name "__builtin_bswap64" then
        (Some R6 :: Some R5 :: nil, Some R5 :: Some R6 :: nil)
      else
        (nil, nil)
  | _ =>
    (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are two: the pseudo [Ocast32signed],
  because it expands to a no-op owing to the representation of 32-bit
  integers as their 64-bit sign extension; and [Ocast32unsigned],
  because it builds on the same magic no-op. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | _ => false
  end.

(** Constraints on constant propagation for builtins *)

Definition builtin_constraints (ef: external_function) :
                                       list builtin_arg_constraint :=
  match ef with
  | EF_builtin id sg => nil
  | EF_vload _ => OK_addressing :: nil
  | EF_vstore _ => OK_addressing :: OK_default :: nil
  | EF_memcpy _ _ => OK_addrstack :: OK_addrstack :: nil
  | EF_annot kind txt targs => map (fun _ => OK_all) targs
  | EF_debug kind txt targs => map (fun _ => OK_all) targs
  | _ => nil
  end.
