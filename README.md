Require Import Coq.Logic.Classical_Prop.

(* --- Tipos básicos --- *)
Parameter World : Type.
Parameter A : Type.

(* --- Propriedades --- *)
Parameter L : World -> Prop.       (* Universo é lógico / coerente *)
Parameter R : A -> World -> Prop.  (* Ato é racional *)
Parameter Int : A -> World -> Prop. (* Ato é intencional *)
Parameter Fis : A -> World -> Prop. (* Ato é físico *)
Parameter Tempo : A -> World -> Prop. (* Ato ocorre no tempo *)

(* --- Modalidades --- *)
Definition box (P : World -> Prop) : Prop := forall w : World, P w.

(* --- Axiomas --- *)
Axiom P2 : box L. 
Axiom P3 : box (fun w => forall a : A, ~ R a w -> ~ L w). 
Axiom P4 : box (fun w => forall a : A, R a w -> Int a w). 
Axiom P5 : box (fun w => forall a : A, Fis a w -> exists w', ~ R a w'). 
Axiom P6 : box (fun w => forall a : A, Tempo a w -> False). 

Axiom R_Necessario : forall a w w', R a w -> R a w'. (* Racionalidade necessária *)

(* --- Teorema TAIR --- *)
Theorem TAIR :
  box (fun w => forall a : A, R a w /\ Int a w /\ ~ Fis a w /\ ~ Tempo a w).
Proof.
  unfold box; intros w a.

  (* Passo 1: Racionalidade do ato *)
  assert (Ra : R a w).
  { destruct (classic (R a w)); try assumption.
    exfalso. apply (P3 w a); [assumption | apply P2]. }

  (* Passo 2: Intencionalidade do ato *)
  assert (Inta : Int a w) by (apply P4; assumption).

  (* Passo 3: Ato não é físico *)
  assert (Fisa : ~ Fis a w).
  { intros F. apply P5 in F. destruct F as [w' HnotR].
    apply HnotR. apply (R_Necessario a w w'); assumption. }

  (* Passo 4: Ato não ocorre no tempo *)
  assert (Ta : ~ Tempo a w).
  { intros T. apply (P6 w a); assumption. }

  (* Conclusão: todas as propriedades juntas *)
  repeat split; assumption.
Qed.
