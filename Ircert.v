Require Import Arith String List Tactics.
Require Import Tactics.
Set Implicit Arguments.

Definition User := nat.
Definition usr_eq := eq_nat_dec.
Definition Channel := nat.
Definition chn_eq := eq_nat_dec.
Definition str_eq := string_dec.
(* TODO: channel name type, and join gets ERR_NOSUCHCHANNEL if it is the invalid constructor *)

Inductive Command : Set :=
  JOIN : User -> Channel -> Command
| PART : User -> Channel -> Command
| PRIVMSG : User -> Channel -> string -> Command
.

Inductive Response : Set :=
| EVN_JOIN : User -> User -> Channel -> Response
| EVN_PART : User -> User -> Channel -> Response
| EVN_MSG : User -> User -> Channel -> string -> Response

| ERR_NOSUCHNICK : User -> User -> Response
| ERR_NOSUCHCHANNEL : User -> Channel -> Response
| ERR_NOTONCHANNEL : User -> Channel -> Response
| ERR_CANNOTSENDTOCHAN : User -> Channel -> Response
.

Definition rsp_eq (r1 r2:Response) : {r1=r2} + {r1<>r2}.
  Hint Resolve usr_eq.
  Hint Resolve chn_eq.
  Hint Resolve str_eq.
  decide equality.
Defined.

Definition Users := list User.
Definition Responses := list Response.
Definition State := list (Channel * Users).

Fixpoint in_users (usr:User) (xs:Users) : bool :=
  match xs with
    | nil => false
    | x :: xs' => if usr_eq usr x
      then true
      else in_users usr xs'
  end.

Fixpoint members (chn:Channel) (xs:State) : Users :=
  match xs with
    | nil => nil
    | (chn' , usrs) :: xs' => if chn_eq chn chn'
      then usrs
      else members chn xs'
  end.

Definition in_channel (usr:User) (chn:Channel) (xs:State) : bool :=
  in_users usr (members chn xs).

Fixpoint in_responses (r:Response) (rs:Responses) : bool :=
  match rs with
    | nil => false
    | r' :: rs' => if rsp_eq r r'
      then true
      else in_responses r rs'
  end.

Fixpoint join_channel (usr:User) (chn:Channel) (xs:State) : Responses :=
  match xs with
    | nil => EVN_JOIN usr usr chn :: nil
    | (chn' , usrs) :: xs' => if chn_eq chn chn' 
      then (map (fun x => EVN_JOIN x usr chn) usrs)
      else
        match join_channel usr chn xs' with
          | es => es
        end
  end.

Ltac ifs' := repeat (match goal with
  | [ |- context[if ?x then _ else _] ] => destruct x
  | [ H : context[if ?x then _ else _] |- _ ] => destruct x
end).

Ltac step :=
  match goal with
    | [ |- ?x ] => congruence
    | [ |- ?x ] => auto
  end.

Ltac ifs :=
ifs'; try (autorewrite with ircert in *); crush.

Ltac cases' :=
intros; try (match goal with
  | [ x : State |- _ ] => induction x
  | [ x : Response |- _ ] => destruct x
  | [ x : Users |- _ ] => induction x
end).

Ltac cases := cases'; crush.

Lemma inside : forall e, in_responses e (e :: nil) = true.
cases; ifs.
Qed. Hint Rewrite inside : ircert.

Lemma when_outside : forall usr chn,
  in_responses (EVN_JOIN usr usr chn) (EVN_JOIN usr usr chn :: nil) = true.
cases; ifs.
Qed. Hint Rewrite when_outside : ircert.

Lemma when_inside : forall usr chn usrs,
  in_users usr usrs = true ->
  in_responses (EVN_JOIN usr usr chn) (map (fun x => EVN_JOIN x usr chn) usrs) = true.
cases; ifs.
Qed. Hint Rewrite when_inside : ircert.

Lemma if_in_chn_then_in_users : forall usr chn xs,
  in_channel usr chn xs = true ->
  in_users usr (members chn xs) = true.
step.
Qed. Hint Rewrite if_in_chn_then_in_users : ircert.

Lemma omg : forall chn (xs ys:Users),
  (if chn_eq chn chn then xs else ys) = xs.
cases; ifs.
Qed. Hint Rewrite omg : ircert.

Lemma hmm : forall usr chn usrs xs,
  in_channel usr chn ((chn, usrs) :: xs) = true ->
  in_users usr usrs = true.
intros. unfold in_channel in H. simpl in H. autorewrite with ircert in H. assumption.
Qed. Hint Rewrite hmm : ircert.
Check map.

Lemma one_map : forall A B (f : A -> B) (x:A) (xs:list A),
  map f (x :: xs) = f x :: map f xs.
auto.
Qed.

Lemma moar : forall r rs,
  in_responses r (r :: rs) = true.
intros. unfold in_responses. auto; ifs.
Qed.

Lemma lemzzz : forall usr joiner chn usrs,
  in_responses (EVN_JOIN usr joiner chn)
  (map (fun x => EVN_JOIN x joiner chn) (usr :: usrs)) = true.
intros. rewrite one_map. apply moar.
Qed.

Lemma for_the_user : forall usr chn usrs,
  in_responses (EVN_JOIN usr usr chn)
  (map (fun x => EVN_JOIN x usr chn) (usr :: usrs)) = true.
intros; apply lemzzz.
Qed.

Lemma hoihoihoi : forall usr usr' usrs,
  in_users usr usrs = false ->
  in_users usr (usr' :: usrs) = true ->
  usr = usr'.
intros. unfold in_users in *. ifs'; step.
Qed.

Lemma cons_preserves_map_prop : forall usr joiner chn a usrs,
  in_responses (EVN_JOIN usr joiner chn)
   (map (fun x : User => EVN_JOIN x joiner chn) usrs) = true ->
  in_responses (EVN_JOIN usr joiner chn)
   (map (fun x : User => EVN_JOIN x joiner chn) (a :: usrs)) = true.
intros; simpl in *; ifs'; auto.
Qed.

Lemma lalala : forall usr joiner chn usrs,
  in_users usr usrs = true ->
  in_responses (EVN_JOIN usr joiner chn)
    (map (fun x => EVN_JOIN x joiner chn) usrs) = true.
intros. induction usrs. auto.
simpl in *; ifs'; step.
Qed.

Lemma lalala2 : forall usr joiner chn xs,
  in_channel usr chn xs = true ->
  in_responses (EVN_JOIN usr joiner chn)
    (map (fun x => EVN_JOIN x joiner chn) (members chn xs)) = true.
intros. unfold in_channel in *. apply lalala. assumption.
Qed.
