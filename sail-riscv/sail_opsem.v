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

Require Export isla.sail_riscv.base.
Require Export isla.sail_riscv.RV64.
Require Export isla.opsem.
Require Import isla.adequacy.
Require Import isla.riscv64.arch.

(*** Relating values *)
Definition byte_to_memory_byte (b : byte) : memory_byte :=
  bitU_of_bool <$> rev (bv_to_bits b).

Global Instance bitU_of_bool_inj : Inj eq eq bitU_of_bool.
Proof. move => [] []; done. Qed.

Global Instance byte_to_memory_byte_inj : Inj eq eq byte_to_memory_byte.
Proof.
  move => x y. rewrite /byte_to_memory_byte/= => ?. simplify_list_eq.
  apply bv_eq. bitblast as n.
  destruct (decide (n = 0)); subst => //.
  destruct (decide (n = 1)); subst => //.
  destruct (decide (n = 2)); subst => //.
  destruct (decide (n = 3)); subst => //.
  destruct (decide (n = 4)); subst => //.
  destruct (decide (n = 5)); subst => //.
  destruct (decide (n = 6)); subst => //.
  destruct (decide (n = 7)); subst => //.
  lia.
Qed.

Lemma byte_to_memory_byte_length b: length (byte_to_memory_byte b) = 8%nat.
Proof. done. Qed.

Local Transparent bv_to_bits.
Lemma byte_to_memory_byte_lookup_Some b i x:
  byte_to_memory_byte b !! i = Some x ↔ (i < 8)%nat ∧ x = bitU_of_bool (Z.testbit (bv_unsigned b) (7 - i)%nat).
Proof. do 8 try destruct i => //=; naive_solver lia. Qed.

Definition bv_to_mword {n1 n2} (b : bv n1) : mword n2 :=
  match N.eq_dec n1 (Z.to_N n2) with
  | left eq => cast_N b eq
  | right _ => bv_0 _
  end.
Arguments bv_to_mword : simpl never.
Definition mword_to_bv {n1 n2} (b : mword n1) : bv n2 :=
  match N.eq_dec (Z.to_N n1) n2 with
  | left eq => cast_N b eq
  | right _ => bv_0 _
  end.
Arguments mword_to_bv : simpl never.

Lemma mword_to_bv_unsigned {n1 n2} (b : mword n1):
  n1 = Z.of_N n2 →
  bv_unsigned (mword_to_bv (n2:=n2) b) = Z.of_N (MachineWord.word_to_N (get_word b)).
Proof.
  move => Heq. rewrite /mword_to_bv. destruct (N.eq_dec (Z.to_N n1) n2) as [E | NE].
  - destruct E. rewrite /MachineWord.word_to_N Z2N.id; last apply bv_unsigned_in_range.
    by rewrite cast_N_refl.
  - contradict NE. subst; by rewrite N2Z.id.
Qed.

Lemma uint_plain_to_bv_unsigned n (b : mword n) :
  0 ≤ n →
  uint b = bv_unsigned b.
Proof. move => ?. rewrite /uint/MachineWord.word_to_N Z2N.id //. by apply bv_unsigned_in_range. Qed.

Lemma eq_vec_to_bv n (b1 b2 : mword n) :
  eq_vec b1 b2 = (bool_decide (b1 = b2)).
Proof.
  case_bool_decide as Hb.
  - rewrite eq_vec_true_iff //.
  - rewrite eq_vec_false_iff //.
Qed.

Lemma N_eq_dec_eq m n (E : m = n) :
  N.eq_dec m n = left E.
Proof.
  destruct (N.eq_dec m n).
  - f_equal. apply Eqdep_dec.UIP_dec. apply N.eq_dec.
  - exfalso. congruence.
Qed.

Lemma access_vec_dec_to_bv  n1 (b : mword n1) z :
  0 ≤ z →
  z < n1 →
  access_vec_dec b z = bitU_of_bool (Z.testbit (bv_unsigned (mword_to_bv (n2:=Z.to_N n1) b)) z).
Proof.
  move => ??. rewrite /access_vec_dec/access_mword_dec/MachineWord.get_bit/MachineWord.Z_idx Z2N.id /mword_to_bv; last lia.
  rewrite N_eq_dec_eq cast_N_refl /get_word //.
Qed.

Lemma mword_to_bv_add_vec {n1 : Z} {n2 : N} (b1 b2 : mword n1) :
  n1 = Z.of_N n2 →
  mword_to_bv (n2:=n2) (add_vec b1 b2) = bv_add (mword_to_bv b1) (mword_to_bv b2).
Proof.
  move => Hn. apply bv_eq.
  rewrite bv_add_unsigned !mword_to_bv_unsigned // get_word_word_binop.
  rewrite /MachineWord.word_to_N/MachineWord.add/get_word.
  rewrite !Z2N.id; [ | apply bv_unsigned_in_range..].
  unfold mword, MachineWord.word, MachineWord.Z_idx in *.
  subst.
  rewrite N2Z.id in b2, b1 |- *.
  bv_solve.
Qed.
Arguments add_vec : simpl never.

Lemma mword_to_bv_update_vec_dec n1 n2 (b : mword n1) b1 z b2:
  bool_of_bitU b1 = Some b2 →
  n1 = Z.of_N n2 →
  z < n1 →
  0 ≤ z →
  mword_to_bv (n2:=n2) (update_vec_dec b z b1) = bv_or
    (bv_and (bv_not (Z_to_bv n2 (1 ≪ z))) (mword_to_bv b))
    (Z_to_bv n2 (bool_to_Z b2 ≪ z)).
Proof.
  move => Hb ???.
  apply bv_eq. rewrite mword_to_bv_unsigned //.
  rewrite /update_vec_dec/opt_def /update_mword_dec Hb.
  rewrite /update_mword_bool_dec get_word_with_word wordToN_setBit/MachineWord.Z_idx;[|lia].
  rewrite bv_or_unsigned bv_and_unsigned bv_not_unsigned !Z_to_bv_unsigned mword_to_bv_unsigned//.
  rewrite /MachineWord.word_to_N/get_word.
  unfold mword, MachineWord.word, MachineWord.Z_idx in b.
  rewrite !Z2N.id; [|by apply bv_unsigned_in_range|lia].
 rewrite !bv_wrap_land.
  bitblast.
Qed.

Definition register_value_to_valu {T} (r : register T) :  T -> valu :=
  match r with
  | R_bitvector_64 misa => fun m => RegVal_Struct [("bits", RVal_Bits (mword_to_bv (n2:=64) m))]
  | R_bitvector_64 mstatus => fun m => RegVal_Struct [("bits", RVal_Bits (mword_to_bv (n2:=64) m))]
  | R_bitvector_1 _ => fun m => RVal_Bits (mword_to_bv (n2:=1) m)
  | R_bitvector_2 _ => fun m => RVal_Bits (mword_to_bv (n2:=2) m)
  | R_bitvector_3 _ => fun m => RVal_Bits (mword_to_bv (n2:=3) m)
  | R_bitvector_4 _ => fun m => RVal_Bits (mword_to_bv (n2:=4) m)
  | R_bitvector_16 _ => fun m => RVal_Bits (mword_to_bv (n2:=16) m)
  | R_bitvector_32 _ => fun m => RVal_Bits (mword_to_bv (n2:=32) m)
  | R_bitvector_64 _ => fun m => RVal_Bits (mword_to_bv (n2:=64) m)
  | R_bitvector_65536 _ => fun m =>  RVal_Bits (mword_to_bv (n2:=65536) m)
  | R_bool _ => fun b => RVal_Bool b
  | R_Privilege _ => fun p => RVal_Enum (match p with | User => "User" | Supervisor => "Supervisor" | Machine => "Machine" end)
  | _ => fun _ => RegVal_Poison
  end.
Global Arguments register_value_to_valu {_} !_ !_ /.

Lemma iris_module_wf_isla_lang :
  iris_module_wf isla_lang.
Proof. move => ?????? Hstep. inv_seq_step; split => //; try destruct κ' => /=; lia. Qed.

(*** operational semantics for [monad] *)
Inductive encoded_instruction :=
| Uncompressed (i : bv 32) | Compressed (i : bv 16).

Record sail_state := SAIL {
  sail_monad : M ();
  sail_regs : regstate;
  sail_mem : mem_map;
  sail_instrs : gmap addr encoded_instruction;
  sail_stopped : bool;
}.

Definition instruction_length (i : encoded_instruction) : mword 64 :=
  match i with
   | Uncompressed ie => mword_of_int 4
   | Compressed ie => mword_of_int 2
   end.

Definition step_cpu (i : encoded_instruction) : M () :=
  dec ← (match i with
   | Uncompressed ie => riscv.encdec_backwards (bv_to_mword ie)
   | Compressed ie => riscv.encdec_compressed_backwards (bv_to_mword ie)
   end);
   PC_val ← Defs.read_reg PC;
   Defs.write_reg nextPC (add_vec PC_val (instruction_length i));;
   R ← execute dec;  if R is RETIRE_SUCCESS then
                          nextPC ← Defs.read_reg nextPC;
                          Defs.write_reg PC nextPC
                        else
                          fail "execution failed!".

Import Interface.

Inductive sail_step : sail_state → option seq_label → sail_state → Prop :=
| SailDone rs h i ins :
  ins !! mword_to_bv (register_lookup PC rs) = Some i →
  sail_step (SAIL (Ret tt) rs h ins false) None (SAIL (step_cpu i) rs h ins false)
| SailStop rs h ins :
  ins !! mword_to_bv (register_lookup PC rs) = None →
  sail_step (SAIL (Ret tt) rs h ins false) (Some (SInstrTrap (mword_to_bv (register_lookup PC rs)))) (SAIL (Ret tt) rs h ins true)
| SailChoose rs h ins ty e v:
  sail_step (SAIL (Next (Choose ty) e) rs h ins false) None (SAIL (e v) rs h ins false)
| SailReadReg T rs h ins e (r : register T) ak v:
  register_lookup r rs = v →
  sail_step (SAIL (Next (RegRead r ak) e) rs h ins false) None (SAIL (e v) rs h ins false)
| SailWriteReg T rs rs' h ins e (r : register T) ak v:
  register_set r v rs = rs' →
  sail_step (SAIL (Next (RegWrite r ak v) e) rs h ins false) None (SAIL (e tt) rs' h ins false)
| SailReadMem rs h ins κ len bs' req e:
  (if read_mem_list h (bv_unsigned req.(ReadReq.pa)) len is Some bs then
    κ = None ∧
    Z_to_bv (8 * len) (little_endian_to_bv 8 bs) = bs'
  else
    bv_unsigned req.(ReadReq.pa) + Z.of_N len ≤ 2 ^ 64 ∧
    set_Forall (λ ad, ¬ (bv_unsigned req.(ReadReq.pa) ≤ bv_unsigned ad < bv_unsigned req.(ReadReq.pa) + Z.of_N len)) (dom h) ∧
    κ = Some (SReadMem req.(ReadReq.pa) bs')) →
  sail_step (SAIL (Next (MemRead len req) e) rs h ins false) κ (SAIL (e (inl (bs', None))) rs h ins false)
| SailWriteMem rs h h' ins e len req κ:
  (if read_mem_list h (bv_unsigned req.(WriteReq.pa)) len is Some _ then
    write_mem len h req.(WriteReq.pa) (bv_unsigned req.(WriteReq.value)) = h' ∧
    κ = None
  else
    bv_unsigned req.(WriteReq.pa) + Z.of_N len ≤ 2 ^ 64 ∧
    set_Forall (λ ad, ¬ (bv_unsigned req.(WriteReq.pa) ≤ bv_unsigned ad < bv_unsigned req.(WriteReq.pa) + Z.of_N len)) (dom h) ∧
    h = h' ∧
    κ = Some (SWriteMem req.(WriteReq.pa) req.(WriteReq.value))) →
  sail_step (SAIL (Next (MemWrite len req) e) rs h ins false) κ (SAIL (e (inl None)) rs h' ins false)
(*| SailWriteEa rs h ins e wk n1 n2:
  sail_step (SAIL (Write_ea wk n1 n2 e) rs h ins false) None (SAIL e rs h ins false)*)
.

Definition sail_module := {|
  m_step := sail_step;
  m_non_ub_state σ := σ.(sail_stopped) ∨ ∃ κ σ', sail_step σ κ σ';
|}.

(*** [mctx]: Evaluation contexts for [monad] *)
Inductive mctx : Type → Type → Type :=
| NilMCtx : mctx () exception
| BindMCtx {A1 A2 E} (f : A1 → monad E A2) (K : mctx A2 E) : mctx A1 E
| TryMCtx {A E1 E2} (f : E1 → monad E2 A) (K : mctx A E2) : mctx A E1.

Fixpoint mctx_interp {A E} (K : mctx A E) : monad E A → M () :=
  match K in (mctx A' E') return (monad E' A' → M _) with
   | NilMCtx => λ e, e
   | BindMCtx f K => λ e, mctx_interp K (e >>= f)
   | TryMCtx f K => λ e, mctx_interp K (try_catch e f)
   end.

Lemma mctx_interp_Choose A E K choose_ty e1:
  @mctx_interp A E K (Next (Choose choose_ty) e1) = Next (Choose choose_ty) (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Read_reg T A E K (r : register T) ak e1:
  @mctx_interp A E K (Next (RegRead r ak) e1) = Next (RegRead r ak) (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_reg T A E K (r : register T) ak e1 v:
  @mctx_interp A E K (Next (RegWrite r ak v) e1) = Next (RegWrite r ak v) (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Read_mem A E K sz req e1:
  @mctx_interp A E K (Next (MemRead sz req) e1) = Next (MemRead sz req) (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_mem A E K sz req e1:
  @mctx_interp A E K (Next (MemWrite sz req) e1) = Next (MemWrite sz req) (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
(*Lemma mctx_interp_Write_ea A E K n1 n2 wk e1:
  @mctx_interp A E K (Write_ea wk n1 n2 e1) = Write_ea wk n1 n2 (mctx_interp K e1).
Proof. elim: K e1 => //=. Qed.*)

(*** [sim]: Simulation relation *)
Definition get_plat_config (reg_name : string) : option valu :=
  match reg_name with
  | "rv_pmp_count" => Some (RegVal_I (sys_pmp_count ()) 64)
  | "rv_enable_misaligned_access" => Some (RVal_Bool (plat_enable_misaligned_access ()))
  | "rv_ram_base" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_ram_base ())))
  | "rv_ram_size" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_ram_size ())))
  | "rv_rom_base" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_rom_base ())))
  | "rv_rom_size" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_rom_size ())))
  | "rv_clint_base" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_clint_base ())))
  | "rv_clint_size" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_clint_size ())))
  | "rv_htif_tohost" => Some (RVal_Bits (mword_to_bv (n2:=64) (plat_htif_tohost ())))
  | "Machine" => Some (RVal_Enum "Machine")
  | _ => None
  end.

Definition get_regval_or_config (reg_name : string) (s : regstate) : option valu :=
  match register_of_string reg_name with
  | Some (GRegister.GReg r) => Some (register_value_to_valu r (register_lookup r s))
  | None => get_plat_config reg_name
  end.

Definition isla_regs_wf (regs : regstate) (isla_regs : reg_map) : Prop :=
  ∀ r vi, isla_regs !! r = Some vi → get_regval_or_config r regs = Some vi. 

Definition private_regs_wf (isla_regs : reg_map) : Prop :=
  isla_regs !! "nextPC" = None.

Record sim_state := SIM {
  sim_regs : regstate;
}.
Add Printing Constructor sim_state.
Global Instance eta_sim_state : Settable _ := settable! SIM <sim_regs>.

Definition sim {A E} (Σ : sim_state) (e1 : monad E A) (K : mctx A E) (e2 : isla_trace) : Prop :=
  ∀ n isla_regs mem sail_instrs isla_instrs,
  isla_regs_wf Σ.(sim_regs) isla_regs →
  private_regs_wf isla_regs →
  (∀ sail_regs' isla_regs' mem',
      isla_regs_wf sail_regs' isla_regs' →
      private_regs_wf isla_regs' →
      dom isla_regs' = dom isla_regs →
      raw_sim sail_module (iris_module isla_lang) n
          (SAIL (Ret tt) sail_regs' mem' sail_instrs false)
          ({| seq_trace := tnil; seq_regs := isla_regs'; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem' |})) →
  raw_sim sail_module (iris_module isla_lang) n
          (SAIL (mctx_interp K e1) Σ.(sim_regs) mem sail_instrs false)
          ({| seq_trace := e2; seq_regs := isla_regs; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem |}).

Definition sim_instr (si : encoded_instruction) (i : isla_trace) :=
  ∀ regs, sim (SIM regs) (step_cpu si) NilMCtx i.

Lemma sim_implies_refines sail_instrs isla_instrs sail_regs isla_regs mem :
  dom isla_instrs = dom sail_instrs →
  isla_regs_wf sail_regs isla_regs →
  private_regs_wf isla_regs →
  (∀ a si ii, sail_instrs !! a = Some si → isla_instrs !! a = Some ii → sim_instr si ii) →
  refines sail_module (SAIL (Ret tt) sail_regs mem sail_instrs false)
          (iris_module isla_lang) (initial_local_state isla_regs, {| seq_instrs := isla_instrs; seq_mem := mem |}).
Proof.
  move => Hdom Hregs Hpriv Hsim. apply: raw_sim_implies_refines => n.
  elim/lt_wf_ind: n sail_regs isla_regs mem Hregs Hpriv.
  move => n IH sail_regs isla_regs mem Hregs Hpriv.
  apply: raw_sim_safe_here => /= Hsafe.
  have {Hsafe} ? : isla_regs !! "PC" = Some (RVal_Bits (mword_to_bv (n2:=64) (register_lookup PC sail_regs))). {
    destruct (isla_regs !! "PC") eqn: HPC.
    - have [<-]:= Hregs "PC" _ ltac:(done). done.
    - move: Hsafe => [[]|]// [?[?[?[? Hsafe]]]]. inv_seq_step.
      revert select (∃ x, _) => -[?[??]]; unfold sail_name in *; simplify_eq.
  }
  destruct (sail_instrs !! mword_to_bv (register_lookup PC sail_regs)) as [si|] eqn: Hsi.
  - move: (Hsi) => /(elem_of_dom_2 _ _ _). rewrite -Hdom. move => /elem_of_dom[ii Hii]. clear Hdom.
    have {}Hsim:= Hsim _ _ _ ltac:(done) ltac:(done) sail_regs.
    apply: raw_sim_step_i. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
    apply: raw_sim_step_s. {
      econstructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: Hsim; [done..|].
    move => sail_regs' isla_regs' mem' Hwf' ??.
    apply IH; [lia|done..].
  - move: (Hsi) => /(not_elem_of_dom). rewrite -Hdom. move => /not_elem_of_dom Hii. clear Hdom.
    constructor => Hsafe. split. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. eexists _. split. {
      apply: (steps_l _ _ _ _ (Some _)); [| by apply: steps_refl].
      constructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: raw_sim_step_i. { by left. }
    move => ???? Hstep. inversion Hstep.
    Unshelve. exact: inhabitant.
Qed.

(*** Lemmas about [sim] *)
Lemma get_plat_config_Some_get_regval r x:
  get_plat_config r = Some x →
  register_of_string r = None.
Proof. unfold get_plat_config. repeat case_match => //. Qed.

(* TODO: Sail should generate something like this. *)
Lemma register_of_string_roundtrip {T} (r : register T) s :
  register_of_string s = Some (GRegister.GReg r) ->
  string_of_register r = s.
Proof.
  unfold register_of_string. simpl.
  repeat match goal with |- match (if ?eq then _ else _) with _ => _ end = _ -> _ => 
    let H := fresh H in destruct eq eqn:H; [
    intro H';
    apply (inj Some) in H';
    destruct r; try discriminate;
    apply GRegister.greg_inj in H';
    rewrite <- H';
    apply String.eqb_eq in H;
    subst;
    reflexivity | clear H ] end.
  discriminate.
Qed.

Lemma get_set_regval_config_ne {T} r (r' : register T) regs regs' v:
  register_set r' v regs = regs' →
  r ≠ string_of_register r' →
  get_regval_or_config r regs' = get_regval_or_config r regs.
Proof.
  move => Hset Hr. rewrite /get_regval_or_config.
  destruct (register_of_string r) as [[T' r1] | ] eqn:Hreg.
  - rewrite <- Hset. rewrite irrelevant_register_set; [reflexivity|]. 
    rewrite register_string_eq.
    apply Bool.not_true_is_false.
    rewrite String.eqb_eq.
    apply register_of_string_roundtrip in Hreg.
    congruence.
  - reflexivity.
Qed.

Lemma sim_done Σ:
  sim Σ (Ret tt) NilMCtx tnil.
Proof. move => ??????? Hdone. by apply: Hdone. Qed.

Lemma sim_mctx_impl A1 A2 E1 E2 Σ e11 e12 K1 K2 e2:
  sim (A:=A1) (E:=E1) Σ e11 K1 e2 →
  mctx_interp K1 e11 = mctx_interp K2 e12 →
  sim (A:=A2) (E:=E2) Σ e12 K2 e2.
Proof. rewrite /sim => ? <-. done. Qed.

Lemma sim_bind A1 A2 E Σ e1 f K e2:
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2 →
  sim (A:=A2) (E:=E) Σ (e1 >>= f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.
Lemma sim_try_catch A E1 E2 Σ e1 f K e2:
  sim (A:=A) (E:=E2) Σ e1 (TryMCtx f K) e2 →
  sim (A:=A) (E:=E1) Σ (try_catch e1 f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind A1 A2 E Σ K e1 f e2:
  sim (A:=A2) Σ (e1 >>= f) K e2 →
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_catch A E1 E2 Σ K e1 f e2:
  sim (A:=A) (E:=E2) Σ (try_catch e1 f) K e2 →
  sim (A:=A) (E:=E1) Σ e1 (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind_Done A1 A2 E Σ K v f e2:
  sim (A:=A2) Σ (f v) K e2 →
  sim (A:=A1) (E:=E) Σ (Ret v) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_Done A E1 E2 Σ K v f e2:
  sim (A:=A) (E:=E2) Σ (Ret v) K e2 →
  sim (A:=A) (E:=E1) Σ (Ret v) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

(* We can't discard binds in the context until we find the try, so we'll
   accumulate them in the term until we get a TryMCtx. *)
Lemma sim_pop_bind_throw A1 A2 E Σ K exn f e2 :
  sim (A:=A1) (E:=E) Σ (throw exn >>= f) K e2 →
  sim (A:=A2) (E:=E) Σ (throw exn) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_binds_throw A1 A2 A3 E Σ K exn f g e2 :
  sim (A:=A1) (E:=E) Σ (throw exn >>= (fun x : A3 => g x >>= f)) K e2 →
  sim (A:=A2) (E:=E) Σ (throw exn >>= g) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_throw A E1 E2 Σ K exn f e2 :
  sim (A:=A) (E:=E2) Σ (f exn) K e2 →
  sim (A:=A) (E:=E1) Σ (throw exn) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_throw_bind A A1 E1 E2 Σ K exn f (e1 : A1 -> monad E1 A) e2 :
  sim (A:=A) (E:=E2) Σ (f exn) K e2 →
  sim (A:=A) (E:=E1) Σ (throw exn >>= e1) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Ltac simplify_eq_dep :=
  repeat match goal with H:@existT _ _ _ _ = @existT _ _ _ _ |- _ =>
    let H' := fresh H in
    specialize (eq_sigT_fst H) as H';
    simplify_eq H';
    apply Eqdep.EqdepTheory.inj_pair2 in H
  end;
  simplify_eq.

Lemma sim_Choose {A E} Σ ty e1 e2 K:
  (∀ v, sim Σ (e1 v) K e2) →
  sim (A:=A) (E:=E) Σ (Next (Choose ty) e1) K e2.
Proof.
  move => Hsim ????????/=. rewrite mctx_interp_Choose.
  apply: raw_sim_step_i. { right. eexists _, _. unshelve constructor. by apply: inhabitant. }
  move => ????/= Hstep. inversion Hstep; simplify_eq_dep. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_Read_reg_l {A E} Σ r ak e1 e2 v K:
  register_lookup (T:=A) r Σ.(sim_regs) = v →
  sim Σ (e1 v) K e2 →
  sim (A:=A) (E:=E) Σ (Next (RegRead r ak) e1) K e2.
Proof.
  move => ? Hsim ????????. rewrite mctx_interp_Read_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq_dep. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_read_reg_ref_l A E Σ (r : register_ref register A) K e2:
  sim Σ (Ret (register_lookup r.(reg) Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg_ref r) K e2.
Proof.
  move => Hsim.
  apply: sim_Read_reg_l; [done|] => ??.
  by apply: Hsim.
Qed.

Lemma sim_read_reg_l A E Σ (r : register A) K e2:
  sim Σ (Ret (register_lookup r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K e2.
Proof.
  move => Hsim.
  apply: sim_Read_reg_l; [done|] => ??.
  by apply: Hsim.
Qed.

Lemma sim_read_reg A E Σ K e2 ann r v:
  v = register_value_to_valu r (register_lookup r Σ.(sim_regs))  →
  sim (A:=A) (E:=E) Σ (Ret (register_lookup r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K (ReadReg (string_of_register r) [] v ann :t: e2).
Proof.
  move => -> Hsim. apply: sim_read_reg_l.
  move => ? isla_regs ??? Hwf??.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (string_of_register r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor => //=. 1: by econstructor.
    simpl. have Hreg:= Hwf (string_of_register r) _ ltac:(done).
    unfold get_regval_or_config in *. rewrite string_of_register_roundtrip in Hreg. simplify_option_eq.
    eexists _, _, _. split_and! => //. by left. }
  by apply: Hsim.
Qed.

(* The v = v' indirection allows us to use reflexivity on the get_plat_config hypothesis to
   check that r is a config register *)
Lemma sim_ReadReg_config A E Σ K e1 e2 ann r v v':
  get_plat_config r = Some v →
  v = v' →
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (ReadReg r [] v' ann :t: e2).
Proof.
  move => Hget <- Hsim ? isla_regs ??? Hwf??.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { by case. }
  have [vi Hvi]: is_Some (isla_regs !! r). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor => //=. 1: by econstructor.
    simpl. have Hr:= Hwf r _ ltac:(done). unfold get_regval_or_config in *.
    erewrite get_plat_config_Some_get_regval in Hr; [|done]. simplify_option_eq.
    eexists _, _, _. split_and! => //. by left. }
  by apply: Hsim.
Qed.

Lemma sim_write_reg {A E} Σ (r : register A) e2 v K v' ann:
  v' = register_value_to_valu r v →
  sim (Σ <|sim_regs := register_set r v Σ.(sim_regs)|>) (Ret tt) K e2 →
  sim (E:=E) Σ (write_reg r v) K (WriteReg (string_of_register r) [] v' ann :t: e2).
Proof.
  destruct Σ => /=.
  move => -> Hsim ? isla_regs ? ?? Hwf ? Hdone. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; clear Hstep; simplify_eq_dep. split; [done|].
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (string_of_register r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor; [done| by econstructor|] => /=.
    eexists _, _, _. done.
  }
  apply: raw_sim_weaken; [apply Hsim => /=| ].
  - move => r' vi'. destruct (decide (r' = string_of_register r)); simplify_eq.
    + rewrite lookup_insert. move => [?].
      unfold get_regval_or_config. rewrite string_of_register_roundtrip register_lookup_set. naive_solver.
    + rewrite lookup_insert_ne //.
      erewrite get_set_regval_config_ne; [|done..]. by apply: Hwf.
  - apply/lookup_insert_None. unfold private_regs_wf in *.
    split; [done|]. move => Hn. rewrite Hn in Hvi. naive_solver.
  - move => ????? Hdom. apply: Hdone; [done..|]. by rewrite Hdom dom_insert_lookup_L.
  - lia.
Qed.

Lemma sim_write_reg_private {E} Σ (r : register _) e2 v K:
  r = nextPC →
  sim (Σ <|sim_regs := register_set r v Σ.(sim_regs)|>) (Ret tt) K e2 →
  sim (E:=E) Σ (write_reg r v) K e2.
Proof.
  destruct Σ => /=.
  move => Heq Hsim ? isla_regs ? ?? Hwf ? Hdone. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; clear Hstep; simplify_eq_dep. split; [done|].
  apply: raw_sim_weaken; [apply Hsim => /=; [|done..]| lia].
  move => ?? Hisla. have ?:= Hwf _ _ ltac:(done).
  erewrite get_set_regval_config_ne with (r' := nextPC) (v := v) (regs := sim_regs0); [done..|].
  move => Hnotpc. compute in Hnotpc. subst. unfold private_regs_wf in *. congruence.
Qed.
(*
Lemma sim_Write_ea {A E} Σ e1 e2 K n2 n1 wk:
  sim Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ (Write_ea wk n1 n2 e1) K e2.
Proof.
  move => Hsim ????????/=. rewrite mctx_interp_Write_ea.
  apply: raw_sim_step_i. { right. eexists _, _. constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.
*)

Lemma sim_write_mem {E} Σ e2 n' (sz : Z) K (v' : bv n') ann res wk' (a' : addr) len' v req:
  (8 * len' = n')%N →
  sz = Z.of_N len' →
  res = RVal_Bool true →
  req.(ConcurrencyInterfaceTypes.Mem_write_request_pa) = a' →
  req.(ConcurrencyInterfaceTypes.Mem_write_request_value) = Some v →
  mword_to_bv v = v' →
  sim Σ (Ret (Ok None)) K e2 →
  sim (E:=E) Σ (sail_mem_write (n := sz) req) K (WriteMem res wk' (RVal_Bits a') (RVal_Bits v') len' None ann :t: e2).
Proof.
  move => ? ? ? ? ? ? Hsim ? isla_regs mem ?? Hwf ? Hdone. subst.
  set a' := ConcurrencyInterfaceTypes.Mem_write_request_pa req.
  set v' := mword_to_bv (n2:=8 * len') v.
  unfold sail_mem_write. simplify_option_eq.
  rewrite mctx_interp_Write_mem.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have {Hsafe}[? Hor] : 0 < Z.of_N len' ∧ (is_Some (read_mem_list mem (bv_unsigned a') len') ∨
    (read_mem_list mem (bv_unsigned a') len' = None ∧
       bv_unsigned a' + Z.of_N len' ≤ 2 ^ 64 ∧
       set_Forall (λ ad, ¬ (bv_unsigned a' ≤ bv_unsigned ad < bv_unsigned a' + Z.of_N len')) (dom mem))). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step.
    revert select (∃ m, _) => -[?[?[?[Ha'[ _ [??]]]]]].
    injection Ha'. intros ?%Eqdep_dec.inj_pair2_eq_dec. 2: { by move => ??; apply decide; apply _. } subst.
    split; [done|]. case_match as Hmem.
    + move: Hmem => /fmap_Some. naive_solver.
    + move: Hmem => /fmap_None. naive_solver.
  }
  constructor => _. split. {
    right. move: Hor => [[? Hm]//|[Hm [??]]].
    all: eexists _, _; eapply SailWriteMem; [done..|].
    all: rewrite /= {1}N2Z.id Hm ?Z2N.id; [> done | done | by apply N2Z.is_nonneg].
  }
  move => ? ? ? ? Hstep. inversion Hstep; simplify_eq_dep; clear Hstep.
  move: H7. rewrite /= {1}N2Z.id. (*rewrite !Z_nat_N !N2Z.id !Heq Z_to_bv_bv_unsigned.*)

  unfold mword_to_bv in v'.
  generalize (sail_mem_write_subproof (Z.of_N len')).
  rewrite N2Z.id /= => EQ_len.
  rewrite (N_eq_dec_eq _ _ EQ_len) in v' |- *.

  move: Hor => [[? Hm]//|[Hm ?]]; rewrite Hm.
  - move => [??]. simplify_eq. eexists _. split. {
      apply: (steps_l' _ _ _ _ _ []); [ |by apply: steps_refl| by rewrite right_id_L].
      econstructor. econstructor; [done| by econstructor|] => /=.
      eexists _, _, v'. split_and! => //.
      by rewrite /read_mem Hm.
    }
    apply: raw_sim_weaken; [by apply Hsim | lia].
  - move => [?[?[??]]]. simplify_eq. eexists _. split. {
      apply: (steps_l' _ _ _ _ _ []); [ |by apply: steps_refl| by rewrite right_id_L].
      econstructor. econstructor; [done| by econstructor|] => /=.
      eexists _, _, v'. split_and! => //.
      rewrite /read_mem Hm /=. split_and! => //.
    }
    apply: raw_sim_weaken; [by apply Hsim| lia].
    Unshelve. apply: inhabitant.
Qed.

Lemma sim_read_mem {E} Σ (sz : Z) e2 K ann ann' rk' (a' : addr) len' len'' sm req:
  len'' = (8 * len')%N →
  sz = Z.of_N len' →
  req.(ConcurrencyInterfaceTypes.Mem_read_request_pa) = a' →
  (∀ r1 (r2 : bv len''), r1 = bv_to_mword r2 → sim Σ ((Ret (Ok (r1, None)))) K (subst_trace (Val_Bits r2) sm e2)) →
  sim (E:=E) Σ (sail_mem_read (n := sz) req) K
      (Smt (DeclareConst sm (Ty_BitVec len'')) ann' :t:
       ReadMem (RVal_Symbolic sm) rk' (RVal_Bits a') len' None ann :t: e2).
Proof.
  move => ? ? ? Hsim. subst. set a' := ConcurrencyInterfaceTypes.Mem_read_request_pa req.
  unfold sail_mem_read, read_mem_bytes.
  move => ? isla_regs mem ?? Hwf ? Hdone. rewrite mctx_interp_Read_mem.
  constructor => Hsafe.
  have {Hsafe}[? Hor] : 0 < Z.of_N len' ∧ (is_Some (read_mem_list mem (bv_unsigned a') len') ∨
    (read_mem_list mem (bv_unsigned a') len' = None ∧
       bv_unsigned a' + Z.of_N len' ≤ 2 ^ 64 ∧
       set_Forall (λ ad, ¬ (bv_unsigned a' ≤ bv_unsigned ad < bv_unsigned a' + Z.of_N len')) (dom mem))). {
    opose proof* Hsafe as He.
    { apply: steps_l'; [|apply steps_refl|done].
      constructor. econstructor; [done|eapply (DeclareConstBitVecS' (bv_0 _))|] => /=. done. }
    move: He => [| {}Hsafe]. { unfold seq_to_val. by case. }
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step.
    revert select (∃ m, _) => -[?[?[?[Ha'[ _ [??]]]]]].
    injection Ha'. intros ?%Eqdep_dec.inj_pair2_eq_dec. 2: { by move => ??; apply decide; apply _. } subst.
    split; [done|]. case_match as Hmem.
    + move: Hmem => /fmap_Some. naive_solver.
    + move: Hmem => /fmap_None. naive_solver.
  }
  split. {
    right. move: Hor => [[? Hm]//|[Hm [??]]].
    all: eexists _, _; eapply SailReadMem; rewrite /= {1}N2Z.id Hm ?Z2N.id; [> done.. | by apply N2Z.is_nonneg ].
  }
  (* Get this rewrite out of the way before we introduce any evars *)
  generalize (sail_mem_read_subproof (Z.of_N len')) => PF.
  rewrite N2Z.id in PF |- *.
  move => ? ? ? ? Hstep. inversion Hstep; simplify_eq_dep; clear Hstep.
  move: H8.
  move: Hor => [[? Hm]//|[Hm [??]]]; rewrite Hm.
  - move => [??]. simplify_eq. eexists _. split. {
      apply: steps_l'.
      { econstructor. econstructor; [done| eapply DeclareConstBitVecS' |] => /=. done. } 2: done.
      apply: (steps_l' _ _ _ _ None); [ |by apply: steps_refl| by rewrite right_id_L ].
      econstructor. econstructor; [done| by econstructor|]; csimpl.
      eexists _, _, _. split_and! => //. { by rewrite /eq_var_name Z.eqb_refl. }
      rewrite /read_mem Hm/=. split_and! => //. by left.
    }
    apply: raw_sim_weaken; [apply Hsim; [ | done..] | lia].
    unfold bv_to_mword.
    by rewrite N_eq_dec_eq.
  - move => [?[??]]. simplify_eq. eexists _. split. {
      apply: steps_l'.
      { econstructor. econstructor; [done| apply: DeclareConstBitVecS'; shelve|] => /=. done. } 2: done.
      apply: (steps_l' _ _ _ _ (Some _)); [ |by apply: steps_refl| by rewrite right_id_L ].
      econstructor. econstructor; [done| by econstructor|]; csimpl.
      eexists _, _, _. split_and! => //. { by rewrite /eq_var_name Z.eqb_refl. }
      by rewrite /read_mem Hm/=.
    }
    apply: raw_sim_weaken; [apply Hsim; [ | done..]| lia].
    unfold bv_to_mword.
    by rewrite N_eq_dec_eq.
    Unshelve. all: apply inhabitant.
Qed.

Lemma sim_assert_exp' E Σ b K e2 s:
  b = true →
  (∀ H, sim Σ (Ret H) K e2) →
  sim (E:=E) Σ (assert_exp' b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp'. destruct b => //. by unfold returnm. Qed.

Lemma sim_assert_exp E Σ b K e2 s:
  b = true →
  sim Σ (Ret tt) K e2 →
  sim (E:=E) Σ (assert_exp b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp. destruct b => //. Qed.

Lemma sim_tcases i A E Σ K e1 ts t:
  ts !! i = Some t →
  sim (A:=A) (E:=E) Σ e1 K t →
  sim (A:=A) (E:=E) Σ e1 K (tcases ts).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor; eapply elem_of_list_lookup_2. done.  }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstBool A E Σ K e1 e2 ann x b:
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Bool b) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x Ty_Bool) ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstBitVec A E Σ K e1 e2 ann x b (v : bv b):
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Bits v) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x (Ty_BitVec b)) ann :t: e2).
Proof.
  move => Hsim ????????. destruct v.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstEnum A E Σ K e1 e2 ann x id c:
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Enum c) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x (Ty_Enum id)) ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DefineConst A E Σ K e1 e2 ann x v e:
  eval_exp e = Some v →
  sim (A:=A) (E:=E) Σ e1 K (subst_trace v x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DefineConst x e) ann :t: e2).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_Branch A E Σ K e1 e2 ann n s:
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (Branch n s ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_BranchAddress A E Σ K e1 e2 ann v:
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (BranchAddress v ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_Assert A E Σ K e1 e2 ann e:
  eval_exp e = Some (Val_Bool true) →
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (Smt (Assert e) ann :t: e2).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Definition eval_assume_val' (regs : regstate) (v : assume_val) : option base_val :=
  match v with
  | AVal_Var r l => v' ← get_regval_or_config r regs;
                   v'' ← read_accessor l v';
                   if v'' is RegVal_Base b then Some b else None
  | AVal_Bool b => Some (Val_Bool b)
  | AVal_Bits b => Some (Val_Bits b)
  | AVal_Enum e => Some (Val_Enum e)
  end.

Fixpoint eval_a_exp' (regs : regstate) (e : a_exp) : option base_val :=
  match e with
  | AExp_Val x _ => eval_assume_val' regs x
  | AExp_Unop uo e' _ =>
    eval_a_exp' regs e' ≫= eval_unop uo
  | AExp_Binop uo e1 e2 _ =>
    v1 ← eval_a_exp' regs e1; v2 ← eval_a_exp' regs e2; eval_binop uo v1 v2
  | AExp_Manyop m es _ => vs ← mapM (eval_a_exp' regs) es; eval_manyop m vs
  | AExp_Ite e1 e2 e3 _ =>
    match eval_a_exp' regs e1 with
    | Some (Val_Bool true) => eval_a_exp' regs e2
    | Some (Val_Bool false) => eval_a_exp' regs e3
    | _ => None
    end
  end.

Lemma eval_assume_val'_sound isla_regs sail_regs e v:
  eval_assume_val isla_regs e = Some v →
  isla_regs_wf sail_regs isla_regs →
  eval_assume_val' sail_regs e = Some v.
Proof.
  destruct e => //=.
  move => /bind_Some[?[? ?]] Hwf.
  have ->:= Hwf _ _ ltac:(done). by subst.
Qed.

Lemma eval_a_exp'_sound isla_regs sail_regs e v:
  eval_a_exp isla_regs e = Some v →
  isla_regs_wf sail_regs isla_regs →
  eval_a_exp' sail_regs e = Some v.
Proof.
  (* TODO: use a proper induction principled instead of a_exp_ott_ind such that it can be used with induction *)
  revert e v. match goal with | |- ∀ e, @?P e => eapply (a_exp_ott_ind (λ es, Forall P es) P) end => /=.
  - move => ????. by apply: eval_assume_val'_sound.
  - move => ?? IH ?? /bind_Some[?[/IH He ?]] ?. by rewrite He.
  - move => ?? IH1 ? IH2 ?? /bind_Some[?[/IH1 He1 /bind_Some[?[/IH2 He2 ?]]]] ?. by rewrite He1 ?He2.
  - move => es /Forall_lookup IHes ??? /bind_Some[?[/mapM_Some /Forall2_same_length_lookup [? Hes] ?]] ?.
    apply/bind_Some. eexists _. split; [|done]. apply/mapM_Some. apply/Forall2_same_length_lookup.
    naive_solver.
  - move => e1 IH1 e2 IH2 e3 IH3 ??.
    destruct (eval_a_exp isla_regs e1) eqn: He1 => // Hb ?.
    have -> := IH1 _ ltac:(done) ltac:(done).
    destruct b as [| [] | |] => //; naive_solver.
  - constructor.
  - move => ????. by constructor.
Qed.

Lemma sim_Assume A E Σ K e1 e2 ann e:
  (eval_a_exp' Σ.(sim_regs) e = Some (Val_Bool true) → sim (A:=A) (E:=E) Σ e1 K e2) →
  sim (A:=A) (E:=E) Σ e1 K (Assume e ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_safe_here => -[[??//]|[?[?[?[??]]]]]. inv_seq_step.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  apply: Hsim; [|done..].
  by apply: eval_a_exp'_sound.
Qed.

Lemma sim_AssumeReg A E Σ K e1 e2 ann r v al:
  ((v' ← get_regval_or_config r Σ.(sim_regs); read_accessor al v') = Some v
    → sim (A:=A) (E:=E) Σ e1 K e2) →
  sim (A:=A) (E:=E) Σ e1 K (AssumeReg r al v ann :t: e2).
Proof.
  move => Hsim ????? Hwf ??.
  apply: raw_sim_safe_here => -[[??//]|[?[?[?[??]]]]]. inv_seq_step.
  revert select (∃ v, _) => -[?[?[?[?[??]]]]]. simplify_eq.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. naive_solver. }
  apply: Hsim; [|done..].
  have ?:= Hwf r _ ltac:(done). simplify_eq.
  apply/bind_Some. naive_solver.
Qed.
