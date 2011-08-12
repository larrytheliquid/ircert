Require Import Arith String List Tactics.
Set Implicit Arguments.

Definition User := nat.
Definition usr_eq := eq_nat_dec.
Definition Channel := nat.
Definition chn_eq := eq_nat_dec.

Inductive Command : Set :=
  JOIN : User -> Channel -> Command
| PART : User -> Channel -> Command
| PRIVMSG : User -> Channel -> string -> Command
.
Inductive Response : Set :=
| EVN_JOIN : User -> User -> Channel -> Response

| ERR_NOSUCHNICK : User -> User -> Response
| ERR_NOSUCHCHANNEL : User -> Channel -> Response
| ERR_CANNOTSENDTOCHAN : User -> Channel -> Response
.

Definition Users := list User.
Definition Responses := list Response.
Definition State := list (Channel * Users).

Fixpoint join_channel (usr:User) (chn : Channel) (xs : State) : Responses * State :=
  match xs with
    | nil => (ERR_NOSUCHCHANNEL usr chn :: nil , xs)
    | (chn' , usrs) :: xs' => if chn_eq chn chn' 
      then
        let usrs' := usr :: usrs in (
          (* TODO: RPL_NAMEREPLY list to usr *)
          map (fun x => EVN_JOIN x usr chn) usrs' , 
          (chn , usrs') :: xs
        )
      else
        match join_channel usr chn xs' with
          | (es , xs'') => (es , (chn' , usrs) :: xs'')
        end
  end.

Definition step (xs:State) (cmd:Command) : Responses * State :=
  match cmd with
    | JOIN usr chn => join_channel usr chn xs
    | _ => (nil , nil)
  end.

