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

(** Abstract syntax and semantics for Patmos assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** Integer registers.  R0 is treated specially because it always reads 
  as zero and is never used as a destination of an instruction. *)

Inductive ireg: Type :=
  | R1:  ireg | R2:  ireg | R3:  ireg | R4:  ireg | R5:  ireg
  | R6:  ireg | R7:  ireg | R8:  ireg | R9:  ireg | R10: ireg
  | R11: ireg | R12: ireg | R13: ireg | R14: ireg | R15: ireg
  | R16: ireg | R17: ireg | R18: ireg | R19: ireg | R20: ireg
  | R21: ireg | R22: ireg | R23: ireg | R24: ireg | R25: ireg
  | R26: ireg | R27: ireg | R28: ireg | R29: ireg | R30: ireg
  | R31: ireg.

Inductive ireg0: Type :=
  | R0: ireg0 | R: ireg -> ireg0.

Coercion R: ireg >-> ireg0.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg0_eq: forall (x y: ireg0), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

(** Special registers. S0 is treated specially because its first 8 bits are
    an alias for the predicate registers, and the rest of it cannot be written
    to. **)

Inductive sreg: Type :=
  | S1:  sreg | S2:  sreg | S3:  sreg | S4:  sreg | S5:  sreg
  | S6:  sreg | S7:  sreg | S8:  sreg | S9:  sreg | S10: sreg
  | S11: sreg | S12: sreg | S13: sreg | S14: sreg | S15: sreg.

Inductive sreg0: Type :=
  | S0: sreg0 | S: sreg -> sreg0.

Coercion S: sreg >-> sreg0.

Lemma sreg_eq: forall (x y: sreg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma sreg0_eq: forall (x y: sreg0), {x=y} + {x<>y}.
Proof. decide equality. apply sreg_eq. Defined.

(** Predicate "registers". P0 is treated specially because it always reads
    as 1, and is never used as a destination of an instruction. *)

Inductive pbit: Type :=
  | P1: pbit | P2: pbit | P3: pbit | P4: pbit | P5: pbit
  | P6: pbit | P7: pbit.

Inductive pbit0: Type :=
  | P0: pbit0 | P: pbit -> pbit0.

Coercion P: pbit >-> pbit0.

Lemma pbit_eq: forall (x y: pbit), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma pbit0_eq: forall (x y: pbit0), {x=y} + {x<>y}.
Proof. decide equality. apply pbit_eq. Defined.

(** We model all registers of the Patmos architecture. *)

Inductive preg: Type :=
  | IR: ireg0 -> preg                    (** integer registers *)
  | SR: sreg0 -> preg                    (** special registers *)
  | PR: pbit0 -> preg                    (** predicate registers *)
  | PC: preg.                           (** program counter *)

Coercion IR: ireg0 >-> preg.
Coercion SR: sreg0 >-> preg.
Coercion PR: pbit0 >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg0_eq. apply sreg0_eq. apply pbit0_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and frame pointer ([FP]). *)

Notation "'SP'" := R31 (only parsing) : asm.
Notation "'FP'" := R30 (only parsing) : asm.

(** Conventional names for special registers. *)
Notation "'SL'"  := S2  (only parsing) : asm.    (** Low part of multiplication result *)
Notation "'SH'"  := S3  (only parsing) : asm.    (** High part of multiplication result *)
Notation "'SS'"  := S5  (only parsing) : asm.    (** Spill pointer *)
Notation "'ST'"  := S6  (only parsing) : asm.    (** Stack pointer *)
Notation "'SRB'" := S7  (only parsing) : asm.    (** Return base address *)
Notation "'SRO'" := S8  (only parsing) : asm.    (** Return address offset *)
Notation "'SXB'" := S9  (only parsing) : asm.    (** Exception return base address *)
Notation "'SXO'" := S10 (only parsing) : asm.    (** Exceotion return address offset *)

Definition label := positive.

Inductive predicate: Type :=
  | Normal:  pbit0 -> predicate
  | Inverse: pbit0 -> predicate.

(** The instruction set. Most instructions correspond exactly to instructions 
    in the actual instruction set of the Patmos processor.
    See the Patmos Reference Handbook for details on each instruction.
    However, some instructions are pseudo-instructions; they expand to canned
    instruction sequences during the printing of the assembly code, and are
    described below.

    A note on immediates: there are various restrictions on the immediate
    operands to Patmos instructions. We do not attempt to capture these
    restrictions in the abstract syntax or in the semantics.
    The assembler will emit an error if immediate operands exceed the
    representable range, and our Patmos generator (file [Asmgen]) is
    careful to respect this range.
    Note also that some instructions are not available in all formats.

    A note on registers: we use named arguments to distinguish the registers
    that are read-only or otherwise handled separately. *)

Inductive instruction : Type :=
  (** 32-bit integer register-register arithmetic *)
  | Padd     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** integer addition *)
  | Psub     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** integer subtraction *)
  | Pxor     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** logical exclusive or *)
  | Psl      (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** shift left *)
  | Psr      (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** shift right *)
  | Psra     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** shift right arithmetic *)
  | Por      (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** logical or *)
  | Pand     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** logical and *)
  | Pnor     (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** logical not or *)
  | Pshadd   (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** shift and add *)
  | Pshadd2  (p: predicate) (rd: ireg) (rs1 rs2: ireg0)        (** shift twice and add *)
  (** 12-bit integer register-immediate arithmetic *)          
  | Paddi    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** integer addition *)
  | Psubi    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** integer subtraction *)
  | Pxori    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical exclusive or *)
  | Psli     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift left *)
  | Psri     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift right *)
  | Psrai    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift right arithmetic *)
  | Pori     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical or *)
  | Pandi    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical and *)
  (** 32-bit integer register-immediate arithmetic *)
  | Paddl    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** integer addition *)
  | Psubl    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** integer subtraction *)
  | Pxorl    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical exclusive or *)
  | Psll     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift left *)
  | Psrl     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift right *)
  | Psral    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift right arithmetic *)
  | Porl     (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical or *)
  | Pandl    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical and *)
  | Pnorl    (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** logical not or *)
  | Pshaddl  (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift and add *)
  | Pshadd2l (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (** shift twice and add *)
  (** Multiplication *)
  | Pmul     (p: predicate) (rs1 rs2: ireg0)                   (** multiply *)
  | Pmulu    (p: predicate) (rs1 rs2: ireg0)                   (** unsigned multiply *)
  (** 32-bit integer register-register comparison *)
  | Pcmpeq   (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** equal *)
  | Pcmpneq  (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** not equal *)
  | Pcmplt   (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** less than *)
  | Pcmple   (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** less than or equal *)
  | Pcmpult  (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** unsigned less than *)
  | Pcmpule  (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** unsigned less than or equal *)
  | Pbtest   (p: predicate) (pd: pbit) (rs1 rs2: ireg0)        (** test bit *)
  (** 5-bit integer register-immediate comparison *)
  | Pcmpeqi  (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** equal *)
  | Pcmpneqi (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** not equal *)
  | Pcmplti  (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** less than *)
  | Pcmplei  (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** less than or equal *)
  | Pcmpulti (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** unsigned less than *)
  | Pcmpulei (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** unsigned less than or equal *)
  | Pbtesti  (p: predicate) (pd: pbit) (rs1: ireg0) (imm: int) (** test bit *)
  (** Predicate arithmetic *)
  | Ppor     (p: predicate) (pd: pbit) (ps1 ps2: predicate)    (** predicate or *)
  | Ppand    (p: predicate) (pd: pbit) (ps1 ps2: predicate)    (** predicate and *)
  | Ppxor    (p: predicate) (pd: pbit) (ps1 ps2: predicate)    (** predicate exclusive or *)
  (** Bitcopy *)
  | Pbcopy   (p: predicate) (rd: ireg) (rs1: ireg0) (imm: int) (ps: predicate) (** bitcopy *)
  (** Special moves *)
  | Pmts     (p: predicate) (rs1: ireg0) (sd: sreg0)           (** move to special *)
  | Pmfs     (p: predicate) (rd: ireg) (ss: sreg0)             (** move from special *)
  (** Load typed *)
  | Plws     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load word from stack cache *)
  | Plwl     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load word from local memory *)
  | Plwc     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load word from data cache *)
  | Plwm     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load word from global memory *)
  | Plhs     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load half-word from stack cache *)
  | Plhl     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load half-word from local memory *)
  | Plhc     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load half-word from data cache *)
  | Plhm     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load half-word from global memory *)
  | Plbs     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load byte from stack cache *)
  | Plbl     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load byte from local memory *)
  | Plbc     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load byte from data cache *)
  | Plbm     (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load byte from global memory *)
  | Plhus    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned half-word from stack cache *)
  | Plhul    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned half-word from local memory *)
  | Plhuc    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned half-word from data cache *)
  | Plhum    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned half-word from global memory *)
  | Plbus    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned byte from stack cache *)
  | Plbul    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned byte from local memory *)
  | Plbuc    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned byte from data cache *)
  | Plbum    (p: predicate) (rd: ireg) (ra: ireg0) (imm: int) (** load unsigned byte from global memory *)
  (** Store typed *)
  | Psws     (p: predicate) (ra rs: ireg0) (imm: int)         (** store word to stack cache *)
  | Pswl     (p: predicate) (ra rs: ireg0) (imm: int)         (** store word to local memory *)
  | Pswc     (p: predicate) (ra rs: ireg0) (imm: int)         (** store word to data cache *)
  | Pswm     (p: predicate) (ra rs: ireg0) (imm: int)         (** store word to global memory *)
  | Pshs     (p: predicate) (ra rs: ireg0) (imm: int)         (** store half-word to stack cache *)
  | Pshl     (p: predicate) (ra rs: ireg0) (imm: int)         (** store half-word to local memory *)
  | Pshc     (p: predicate) (ra rs: ireg0) (imm: int)         (** store half-word to data cache *)
  | Pshm     (p: predicate) (ra rs: ireg0) (imm: int)         (** store half-word to global memory *)
  | Psbs     (p: predicate) (ra rs: ireg0) (imm: int)         (** store byte to stack cache *)
  | Psbl     (p: predicate) (ra rs: ireg0) (imm: int)         (** store byte to local memory *)
  | Psbc     (p: predicate) (ra rs: ireg0) (imm: int)         (** store byte to data cache *)
  | Psbm     (p: predicate) (ra rs: ireg0) (imm: int)         (** store byte to global memory *)
  (** Register stack control *)
  | Psens    (p: predicate) (rs: ireg0)                       (** ensure usage of stack cache *)
  | Psspill  (p: predicate) (rs: ireg0)                       (** spill tail of stack cache *)
  (** Immediate stack control *)
  | Psres    (p: predicate) (imm: int)                        (** reserve space in stack cache *)
  | Psensi   (p: predicate) (imm: int)                        (** ensure usage of stack cache *)
  | Psfree   (p: predicate) (imm: int)                        (** free space in stack cache *)
  | Psspilli (p: predicate) (imm: int)                        (** spill tail of stack cache *)
  (** Immediate control-flow functions *)
  | Pcallnd  (p: predicate) (imm: int)                        (** non-delayed function call *)
  | Pcall    (p: predicate) (imm: int)                        (** function call *)
  | Pbrnd    (p: predicate) (imm: int)                        (** non-delayed local branch *)
  | Pbr      (p: predicate) (imm: int)                        (** local branch *)
  | Pbrcfnd  (p: predicate) (imm: int)                        (** non-delayed branch *)
  | Pbrcf    (p: predicate) (imm: int)                        (** branch *)
  | Ptrap    (p: predicate) (imm: int)                        (** system call *)
  (** Register control-flow functions *)                                              
  | Pcallndr (p: predicate) (ra: ireg0)                       (** non-delayed function call *)
  | Pcallr   (p: predicate) (ra: ireg0)                       (** function call *)
  | Pbrndr   (p: predicate) (ra: ireg0)                       (** non-delayed local branch *)
  | Pbrr     (p: predicate) (ra: ireg0)                       (** local branch *)
  | Pbrcfndr (p: predicate) (ra ro: ireg0)                    (** non-delayed branch *)
  | Pbrcfr   (p: predicate) (ra ro: ireg0)                    (** branch *)
  (** Return functions *)
  | Pretnd   (p: predicate)                                   (** non-delayed return *)
  | Pret     (p: predicate)                                   (** return *)
  | Pxretnd  (p: predicate)                                   (** non-delayed return from exception *)
  | Pxret    (p: predicate)                                   (** return from exception *)
  (** Pseudo-instructions *)
  | Pallocframe (sz: Z) (pos: ptrofs)                         (** allocate a new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)  (** deallocate stack frame and restore previous frame *)
  | Plabel   (lbl: label)                                     (** define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs)          (** load the address of a symbol *)
  | Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (** load the high part of the address of a symbol *)
  | Pbtbl    (r: ireg) (tbl: list label)                      (** N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg) -> builtin_res preg -> instruction (** build-in function *)
  | Pnop: instruction.

(** The pseudo-instructions are the following:
  NOTE/TODO: THIS IS COPIED VERBATIM FROM RISC-V

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

- [Ploadli rd ival]: load an immediate 64-bit integer into an integer
  register rd.  Expands to a load from an address in the constant data section,
  using the integer register x31 as temporary:
<<
        lui x31, %hi(lbl)
        ld rd, %lo(lbl)(x31)
lbl:
        .quad ival
>>

- [Ploadfi rd fval]: similar to [Ploadli] but loads a double FP constant fval
  into a float register rd.

- [Ploadsi rd fval]: similar to [Ploadli] but loads a singe FP constant fval
  into a float register rd.

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        mv      x30, sp
        sub     sp,  sp, #sz
        sw      x30, #pos(sp)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is just an increment of [sp]:
<<
        add     sp,  sp, #sz
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        la      x31, table
        add     x31, x31, reg
        jr      x31
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pseq rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        sltiu   rd, rd, 1
>>
  The [xor] is omitted if one of [rs1] and [rs2] is [x0].

- [Psne rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        sltu    rd, x0, rd
>>
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_sig: signature; fn_code: code }.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tint] and boolean registers to either [Vzero] or [Vone]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

(** We maintain that R0 always equals 0 and P0 always equals 1. *)

Definition getR0 (rs: regset) (r: ireg0) : val :=
  match r with
  | R0 => Vint Int.zero
  | R r => rs r
  end.

Definition getP0 (rs: regset) (p: pbit0) : val :=
  match p with
  | P0 => Vone
  | P p => rs p
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (getR0 a b) (at level 1) : asm.
Notation "a ### b" := (getP0 a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 20-bit high part [%hi(symbol + offset)] and 
  a 12-bit low part [%lo(symbol + offset)]. *)

Parameter low_half: genv -> ident -> ptrofs -> ptrofs.
Parameter high_half: genv -> ident -> ptrofs -> val.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
  Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)
(** TODO: Consider rewriting this based on the PPC code *)

(*
Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  | Ofslow id delta => low_half ge id delta
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: ireg) (ofs: offset) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) with
  | None => Stuck
  | Some v => Next (nextinstr (rs#d <- v)) m
  end.

Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: ireg) (ofs: offset) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

*)

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

(** Removing everything but the last 5 bits from a value for shift instructions *)
Definition trim_shift (v: val) : val := Val.shru (Val.shl v (Vint (Int.repr 27))) (Vint (Int.repr 27)).

(** Unpacking predicates into predicate register bits to evaluate operators on them *)
Definition eval_pred_op (op: val -> val -> val) (p1 p2: predicate) (rs: regset): val :=
  match p1, p2 with
  | Normal pb1, Normal pb2   => op rs###pb1 rs###pb2
  | Normal pb1, Inverse pb2  => op rs###pb1 (Val.notint rs###pb2)
  | Inverse pb1, Normal pb2  => op (Val.notint rs###pb1) rs###pb2
  | Inverse pb1, Inverse pb2 => op (Val.notint rs###pb1) (Val.notint rs###pb2)
  end.

Definition eval_pred (p: predicate) (rs: regset): val :=
  match p with
  | Normal pb  => rs###pb
  | Inverse pb => Val.notint rs###pb
  end.

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** 32-bit integer register-register arithmetic *)
  | Padd    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.add rs##rs1 rs##rs2))) m
  | Psub    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.sub rs##rs1 rs##rs2))) m
  | Pxor    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.xor rs##rs1 rs##rs2))) m
  | Psl     p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.shl rs##rs1 (trim_shift rs##rs2)))) m
  | Psr     p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.shru rs##rs1 (trim_shift rs##rs2)))) m
  | Psra    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.shr rs##rs1 (trim_shift rs##rs2)))) m
  | Por     p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.or rs##rs1 rs##rs2))) m
  | Pand    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.and rs##rs1 rs##rs2))) m
  | Pnor    p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.notint (Val.or rs##rs1 rs##rs2)))) m
  | Pshadd  p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.add (Val.shl rs##rs1 Vone) rs##rs2))) m
  | Pshadd2 p rd rs1 rs2 => Next (nextinstr (rs#rd <- (Val.add (Val.shl rs##rs1 (Vint (Int.repr 2))) rs##rs2))) m
  (** 12-bit integer register-immediate arithmetic *)
  | Paddi   p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.add rs##rs1 (Vint imm)))) m
  | Psubi   p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.sub rs##rs1 (Vint imm)))) m
  | Pxori   p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.xor rs##rs1 (Vint imm)))) m
  | Psli    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shl rs##rs1 (trim_shift (Vint imm))))) m
  | Psri    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shru rs##rs1 (trim_shift (Vint imm))))) m
  | Psrai   p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shr rs##rs1 (trim_shift (Vint imm))))) m
  | Pori    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.or rs##rs1 (Vint imm)))) m
  | Pandi   p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.and rs##rs1 (Vint imm)))) m
  (** 32-bit integer register-immediate arithmetic *)
  | Paddl    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.add rs##rs1 (Vint imm)))) m
  | Psubl    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.sub rs##rs1 (Vint imm)))) m
  | Pxorl    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.xor rs##rs1 (Vint imm)))) m
  | Psll     p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shl rs##rs1 (trim_shift (Vint imm))))) m
  | Psrl     p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shru rs##rs1 (trim_shift (Vint imm))))) m
  | Psral    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.shr rs##rs1 (trim_shift (Vint imm))))) m
  | Porl     p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.or rs##rs1 (Vint imm)))) m
  | Pandl    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.and rs##rs1 (Vint imm)))) m
  | Pnorl    p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.notint (Val.or rs##rs1 (Vint imm))))) m
  | Pshaddl  p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.add (Val.shl rs##rs1 Vone) (Vint imm)))) m
  | Pshadd2l p rd rs1 imm => Next (nextinstr (rs#rd <- (Val.add (Val.shl rs##rs1 (Vint (Int.repr 2))) (Vint imm)))) m
  (** Multiplication *)
  | Pmul  p rs1 rs2 => Next (nextinstr (rs#SL <- (Val.mul rs##rs1 rs##rs2)
                                          #SH <- (Val.mulhs rs##rs1 rs##rs2))) m
  | Pmulu p rs1 rs2 => Next (nextinstr (rs#SL <- (Val.mul rs##rs1 rs##rs2)
                                          #SH <- (Val.mulhu rs##rs1 rs##rs2))) m
  (** 32-bit integer register-register comparison *)
  | Pcmpeq  p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmp Ceq rs##rs1 rs##rs2))) m
  | Pcmpneq p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmp Cne rs##rs1 rs##rs2))) m
  | Pcmplt  p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmp Clt rs##rs1 rs##rs2))) m
  | Pcmple  p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmp Cle rs##rs1 rs##rs2))) m
  | Pcmpult p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmpu (Mem.valid_pointer m) Clt rs##rs1 rs##rs2))) m
  | Pcmpule p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmpu (Mem.valid_pointer m) Cle rs##rs1 rs##rs2))) m
  | Pbtest  p pd rs1 rs2 => Next (nextinstr (rs#pd <- (Val.cmp Cne (Val.and rs##rs1 (Val.shl Vone rs##rs2)) Vzero))) m
  (** 5-bit integer register-immediate comparison *)
  | Pcmpeqi  p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmp Ceq rs##rs1 (Vint imm)))) m
  | Pcmpneqi p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmp Cne rs##rs1 (Vint imm)))) m
  | Pcmplti  p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmp Clt rs##rs1 (Vint imm)))) m
  | Pcmplei  p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmp Cle rs##rs1 (Vint imm)))) m
  | Pcmpulti p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmpu (Mem.valid_pointer m) Clt rs##rs1 (Vint imm)))) m
  | Pcmpulei p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmpu (Mem.valid_pointer m) Cle rs##rs1 (Vint imm)))) m
  | Pbtesti  p pd rs1 imm => Next (nextinstr (rs#pd <- (Val.cmp Cne (Val.and rs##rs1 (Val.shl Vone (Vint imm))) Vzero))) m
  (** Predicate arithmetic *)
  | Ppor  p pd ps1 ps2 => Next (nextinstr (rs#pd <- (eval_pred_op Val.or ps1 ps2 rs))) m
  | Ppand p pd ps1 ps2 => Next (nextinstr (rs#pd <- (eval_pred_op Val.and ps1 ps2 rs))) m
  | Ppxor p pd ps1 ps2 => Next (nextinstr (rs#pd <- (eval_pred_op Val.xor ps1 ps2 rs))) m
  (** Bitcopy *)
  | Pbcopy p rd rs1 imm ps => Next (nextinstr (rs#rd <- (Val.or (Val.and rs##rs1 (Val.notint (Val.shl Vone (Vint imm)))) (Val.shl (eval_pred ps rs) (Vint imm))))) m
  (** Special moves *)
  (** TODO: ADD TO SEMANTICS THAT S0 is P0..P7 *)
  | Pmts p rs1 sd =>  Next (nextinstr (rs#sd <- rs#rs1)) m
  | Pmfs p rd ss  =>  Next (nextinstr (rs#rd <- rs#ss)) m
  (** Load type *)
  |
  |
  end.

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
               | R5  => X5  | R6  => X6  | R7  => X7
  | R8  => X8  | R9  => X9  | R10 => X10 | R11 => X11
  | R12 => X12 | R13 => X13 | R14 => X14 | R15 => X15
  | R16 => X16 | R17 => X17 | R18 => X18 | R19 => X19
  | R20 => X20 | R21 => X21 | R22 => X22 | R23 => X23
  | R24 => X24 | R25 => X25 | R26 => X26 | R27 => X27
  | R28 => X28 | R29 => X29 | R30 => X30

  | Machregs.F0  => F0  | Machregs.F1  => F1  | Machregs.F2  => F2  | Machregs.F3  => F3
  | Machregs.F4  => F4  | Machregs.F5  => F5  | Machregs.F6  => F6  | Machregs.F7  => F7
  | Machregs.F8  => F8  | Machregs.F9  => F9  | Machregs.F10 => F10 | Machregs.F11 => F11
  | Machregs.F12 => F12 | Machregs.F13 => F13 | Machregs.F14 => F14 | Machregs.F15 => F15
  | Machregs.F16 => F16 | Machregs.F17 => F17 | Machregs.F18 => F18 | Machregs.F19 => F19
  | Machregs.F20 => F20 | Machregs.F21 => F21 | Machregs.F22 => F22 | Machregs.F23 => F23
  | Machregs.F24 => F24 | Machregs.F25 => F25 | Machregs.F26 => F26 | Machregs.F27 => F27
  | Machregs.F28 => F28 | Machregs.F29 => F29 | Machregs.F30 => F30 | Machregs.F31 => F31
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#SP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

(** Execution of the instruction at [rs PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs SP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs#X31 <- Vundef))) ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments rs m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PC = Vnullptr ->
      rs X10 = Vint r ->
      final_state (State rs m) r.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2).
  { intros. inv H; inv H0; congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; intros. inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs).
  { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. }
  inv H. unfold Vzero in H0. red; intros; red; intros.
  inv H; rewrite H0 in *; eelim NOTNULL; eauto.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.
