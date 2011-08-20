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

Fixpoint in_channel (usr:User) (chn:Channel) (xs:State) : bool :=
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
      then EVN_JOIN usr usr chn :: nil
      else
        match join_channel usr chn xs' with
          | es => es
        end
  end.

Ltac ifs :=
repeat (match goal with
  | [ |- context[if ?x then _ else _] ] => destruct x
  | [ H : context[if ?x then _ else _] |- _ ] => destruct x
  | [ H : context[in_users ?usr ?usrs] |- _ ] => destruct (in_users usr usrs)
end); try (autorewrite with ircert in *); crush.

Ltac cases' :=
intros; match goal with
  | [ x : State |- _ ] => induction x
  | [ x : Response |- _ ] => destruct x
  | [ x : Users |- _ ] => induction x
end.

Ltac cases := cases'; crush.

Lemma fooooo usr chn xs :
  join_channel usr chn xs = (EVN_JOIN usr usr chn) :: nil.
cases; ifs.
Qed.

Lemma inside : forall e, in_responses e (e :: nil) = true.
cases; ifs.
Qed. Hint Rewrite inside : ircert.

Lemma map_inside : forall usr chn usrs,
  in_users usr usrs = true ->
  in_responses (EVN_JOIN usr usr chn) (map (fun x => EVN_JOIN x usr chn) usrs) = true.
cases; ifs.
Qed.

Lemma fooooo2 usr chn xs :
  in_responses (EVN_JOIN usr usr chn) (join_channel usr chn xs) = true.
cases; ifs. 
Qed.

