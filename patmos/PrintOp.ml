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

(** Pretty-printing of operators, conditions, addressing modes *)

open Printf
open Camlcoq
open Integers
open Op

let comparison_name = function
  | Ceq -> "=="
  | Cne -> "!="
  | Clt -> "<"
  | Cle -> "<="
  | Cgt -> ">"
  | Cge -> ">="

let print_condition reg pp = function
  | (Ccomp c, [r1;r2]) ->
      fprintf pp "%a %ss %a" reg r1 (comparison_name c) reg r2
  | (Ccompu c, [r1;r2]) ->
      fprintf pp "%a %su %a" reg r1 (comparison_name c) reg r2
  | (Ccompimm(c, n), [r1]) ->
      fprintf pp "%a %ss %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | (Ccompuimm(c, n), [r1]) ->
      fprintf pp "%a %su %ld" reg r1 (comparison_name c) (camlint_of_coqint n)
  | _ ->
      fprintf pp "<bad condition>"

let print_operation reg pp = function
  | Omove, [r1] -> reg pp r1
  | Ointconst n, [] -> fprintf pp "%ld" (camlint_of_coqint n)
  | Ofloatconst n, [] -> fprintf pp "%F" (camlfloat_of_coqfloat n)
  | Osingleconst n, [] -> fprintf pp "%Ff" (camlfloat_of_coqfloat32 n)
  | Oaddrsymbol(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Oaddrstack ofs, [] ->
      fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | Ocast8signed, [r1] -> fprintf pp "int8signed(%a)" reg r1
  | Ocast16signed, [r1] -> fprintf pp "int16signed(%a)" reg r1
  | Oadd, [r1;r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Oaddimm n, [r1] -> fprintf pp "%a + %ld" reg r1 (camlint_of_coqint n)
  | Oneg, [r1] -> fprintf pp "-(%a)" reg r1
  | Osub, [r1;r2] -> fprintf pp "%a - %a" reg r1 reg r2
  | Omul, [r1;r2] -> fprintf pp "%a * %a" reg r1 reg r2
  | Omulhs, [r1;r2] -> fprintf pp "%a *hs %a" reg r1 reg r2
  | Omulhu, [r1;r2] -> fprintf pp "%a *hu %a" reg r1 reg r2
  | Oand, [r1;r2] -> fprintf pp "%a & %a" reg r1 reg r2
  | Oandimm n, [r1] -> fprintf pp "%a & %ld" reg r1 (camlint_of_coqint n)
  | Oor, [r1;r2] -> fprintf pp "%a | %a" reg r1 reg r2
  | Oorimm n, [r1] ->  fprintf pp "%a | %ld" reg r1 (camlint_of_coqint n)
  | Oxor, [r1;r2] -> fprintf pp "%a ^ %a" reg r1 reg r2
  | Oxorimm n, [r1] -> fprintf pp "%a ^ %ld" reg r1 (camlint_of_coqint n)
  | Oshl, [r1;r2] -> fprintf pp "%a << %a" reg r1 reg r2
  | Oshlimm n, [r1] -> fprintf pp "%a << %ld" reg r1 (camlint_of_coqint n)
  | Oshr, [r1;r2] -> fprintf pp "%a >>s %a" reg r1 reg r2
  | Oshrimm n, [r1] -> fprintf pp "%a >>s %ld" reg r1 (camlint_of_coqint n)
  | Oshru, [r1;r2] -> fprintf pp "%a >>u %a" reg r1 reg r2
  | Oshruimm n, [r1] -> fprintf pp "%a >>u %ld" reg r1 (camlint_of_coqint n)
  | Oshrximm n, [r1] -> fprintf pp "%a >>x %ld" reg r1 (camlint_of_coqint n)
  | Ocmp c, args -> print_condition reg pp (c, args)
  | _ -> fprintf pp "<bad operator>"

let print_addressing reg pp = function
  | Aindexed n, [r1] -> fprintf pp "%a + %Ld" reg r1 (camlint64_of_ptrofs n)
  | Aindexed2, [r1; r2] -> fprintf pp "%a + %a" reg r1 reg r2
  | Aglobal(id, ofs), [] ->
      fprintf pp "\"%s\" + %Ld" (extern_atom id) (camlint64_of_ptrofs ofs)
  | Abased(id, ofs), [r1] -> fprintf pp "%s + %ld + %a" (extern_atom id) (camlint_of_coqint ofs) reg r1
  | Ainstack ofs, [] -> fprintf pp "stack(%Ld)" (camlint64_of_ptrofs ofs)
  | _ -> fprintf pp "<bad addressing>"
