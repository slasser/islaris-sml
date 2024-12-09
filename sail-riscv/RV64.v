(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Export SailStdpp.Base.
Require Export SailStdpp.Prompt_monad.
Require Export SailStdpp.MachineWord.
Require Export RV64.riscv_types.
Require Export Riscv_common.riscv_extras.
Require Export RV64.riscv.
Export RV64.riscv_types.Defs.
Require Import stdpp.bitvector.tactics.
Require Import isla.base.

Local Arguments N.mul : simpl never.


Local Open Scope Z_scope.

(* This file should not depend on anything in islaris since it is quite slow to compile. *)

Lemma get_word_word_binop {n} f (b1 b2 : mword n):
  get_word (word_binop f b1 b2) = f _ (get_word b1) (get_word b2).
Proof. by destruct n. Qed.

Lemma get_word_with_word n (b : mword n) f:
  (get_word (with_word (P:=id) f b)) = f (get_word b).
Proof. by destruct n. Qed.

Lemma nth_error_lookup_some {A : Type} (l : list A) (i : nat) (x : A) :
  l !! i = Some x <-> List.nth_error l i = Some x.
split.
* move => H.
  have := (lookup_lt_Some _ _ _ H) => I.
  apply nth_lookup_Some with (d := x) in H.
  rewrite -H -nth_error_nth' //.
* move => H.
  destruct (l !! i) eqn:L.
  - apply nth_error_nth with (d:=x) in H.
    rewrite nth_lookup L in H.
    simpl in H.
    by subst.
  - apply lookup_ge_None_1 in L.
    have := nth_error_Some l i.
    rewrite H.
    intuition (congruence || lia).
Qed.

(*
Lemma bitblast_bounded_WordToN n (b : Word.word n):
  BitblastBounded (Z.of_N (Word.wordToN b)) (Z.of_nat n).
Proof.
  constructor. split; [lia|]. have := Word.wordToN_bound b.
  have {2}->: n = Z.to_nat (Z.of_nat n) by lia.
  move => /lt_Npow2. lia.
Qed.
Global Hint Resolve bitblast_bounded_WordToN | 15 : bitblast.
(* Also allow for terms where the Sail shim appears *)
Global Hint Unfold MachineWord.word : bitblast.
*)
Lemma wordToN_setBit n (z : N) (w : MachineWord.word n) b:
  (z < n)%N →
  Z.of_N (MachineWord.word_to_N (MachineWord.set_bit w z b)) =
    Z.lor (Z.land (Z.lnot (1 ≪ Z.of_N z)) (Z.of_N (MachineWord.word_to_N w))) (bool_to_Z b ≪ Z.of_N z).
Proof.
  move => ?.
  rewrite /MachineWord.word_to_N/MachineWord.set_bit/MachineWord.update_slice/MachineWord.slice.
  rewrite !Z2N.id; try apply bv_unsigned_in_range.
  rewrite !bv_concat_unsigned; [ | lia..].
  rewrite !bv_extract_unsigned.
  unfold MachineWord.word in w.
  reduce_closed (N.of_nat 1).
  bitblast as i.
  - replace (i - Z.of_N z) with 0 by lia.
    by destruct b.
  - replace (i + Z.of_N 0) with i by lia.
    done.
Qed.

Lemma bit_to_bool_false b:
  b = B0 →
  bit_to_bool b = Interface.Ret false.
Proof. by move => ->. Qed.
Lemma bit_to_bool_true b:
  b = B1 →
  bit_to_bool b = Interface.Ret true.
Proof. by move => ->. Qed.
Lemma bitU_of_bool_B0 b :
  b = false →
  bitU_of_bool b = B0.
Proof. by move => ->. Qed.
Lemma bitU_of_bool_B1 b :
  b = true →
  bitU_of_bool b = B1.
Proof. by move => ->. Qed.
Lemma access_vec_dec_concrete x n (b : mword n) z:
  access_vec_dec b z = x →
  access_vec_dec b z = x.
Proof. by move => ->. Qed.

Lemma if_true b A (e1 e2 : A):
  b = true →
  (if b then e1 else e2) = e1.
Proof. naive_solver. Qed.
Lemma if_false b A (e1 e2 : A):
  b = false →
  (if b then e1 else e2) = e2.
Proof. naive_solver. Qed.

Lemma just_list_mapM {A} (l : list (option A)):
  just_list l = mapM (M := option) id l.
Proof. elim: l => //= -[|]//= ?? ->. case_match => //. Qed.

Lemma byte_chunks_reshape {A} n (l : list A):
  (length l = n * 8)%nat →
  byte_chunks l = Some (reshape (replicate n 8%nat) l).
Proof.
  move Hlen: (length l) => len.
  elim/lt_wf_ind: len l n Hlen => len IH l n ?. subst.
  destruct l => //=. { by destruct n. }
  do 7 (destruct l => /=; [lia|]). move => ?.
  have ?: (length l = ((n-1) * 8))%nat by lia.
  erewrite IH; [..|done]; [|simpl;lia|done].
  have {2}-> : (n = S (n-1)) by lia.
  by rewrite /= take_0 drop_0.
Qed.

Lemma cast_Z_id T m n x E : @cast_Z T m n x E = eq_rect m T x n E.
Proof. destruct E. apply cast_Z_refl. Qed.

Lemma length_bits_of_bytes l:
  (∀ x, x ∈ l → length x = 8%nat) →
  length (bits_of_bytes l) = (length l * 8)%nat.
Proof.
  move => Hf.
  rewrite /bits_of_bytes concat_join map_fmap join_length -list_fmap_compose /compose.
  rewrite (sum_list_fmap_same 8) //.
  apply list.Forall_forall => ?. rewrite /bits_of/= map_fmap fmap_length. apply: Hf.
Qed.

Lemma length_bits_of_mem_bytes l:
  (∀ x, x ∈ l → length x = 8%nat) →
  length (bits_of_mem_bytes l) = (length l * 8)%nat.
Proof.
  move => Hf. rewrite length_bits_of_bytes ?rev_length // => ?.
  rewrite rev_reverse elem_of_reverse. apply: Hf.
Qed.

Lemma bool_of_bitU_of_bool b:
  bool_of_bitU (bitU_of_bool b) = Some b.
Proof. by destruct b. Qed.

Record register_ref_record := RegRef {
  reg_ref_type : Type;
  reg_ref_ref : register_ref register reg_ref_type
}.
Arguments RegRef {_} _.
