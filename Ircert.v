Require Import Arith String List Tactics.
Set Implicit Arguments.

Definition User := nat.
Definition usr_eq := eq_nat_dec.
Definition Channel := nat.
Definition chn_eq := eq_nat_dec.
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

Definition Users := list User.
Definition Responses := list Response.
Definition State := list (Channel * Users).

Fixpoint in_channel (usr:User) (xs:Users) : bool :=
  match xs with
    | nil => false
    | x :: xs' => if usr_eq usr x
      then true
      else in_channel usr xs'
  end.

(* TODO: RPL_NAMEREPLY list to usr *)
Fixpoint join_channel (usr:User) (chn:Channel) (xs:State) : Responses * State :=
  let joined := fun usrs => (
    map (fun x => EVN_JOIN x usr chn) (usr :: usrs) , 
    (chn , usr :: usrs) :: xs
  ) in

  match xs with
    | nil => joined nil
    | (chn' , usrs) :: xs' => if chn_eq chn chn' 
      then if in_channel usr usrs 
        then (nil , xs)
        else joined usrs
      else
        match join_channel usr chn xs' with
          | (es , xs'') => (es , (chn' , usrs) :: xs'')
        end
  end.

Fixpoint part_channel (usr:User) (chn:Channel) (xs:State) : Responses * State :=
  match xs with
    | nil => (ERR_NOSUCHCHANNEL usr chn :: nil , xs)
    | (chn' , usrs) :: xs' => if chn_eq chn chn' 
      then if in_channel usr usrs
        then     
          let usrs' := remove usr_eq usr usrs in (
            map (fun x => EVN_PART x usr chn) usrs , 
            (chn , usrs') :: xs'
          )
        else
          (ERR_NOTONCHANNEL usr chn :: nil , xs)
      else
        match part_channel usr chn xs' with
          | (es , xs'') => (es , (chn' , usrs) :: xs'')
        end
  end.

Fixpoint msg_channel (usr:User) (chn:Channel) (msg:string) (xs:State)
  : Responses * State :=
  match xs with
    | nil => (ERR_NOSUCHNICK usr chn :: nil , xs)
    | (chn' , usrs) :: xs' => if chn_eq chn chn' 
      then if in_channel usr usrs
        then
          let usrs' := remove usr_eq usr usrs in (
            map (fun x => EVN_MSG x usr chn msg) usrs' , 
            xs
          )
        else (ERR_CANNOTSENDTOCHAN usr chn :: nil , xs)
      else
        match msg_channel usr chn msg xs' with
          | (es , xs'') => (es , (chn' , usrs) :: xs'')
        end
  end.

Definition step (xs:State) (cmd:Command) : Responses * State :=
  match cmd with
    | JOIN usr chn => join_channel usr chn xs
    | PART usr chn => part_channel usr chn xs
    | PRIVMSG usr chn msg => msg_channel usr chn msg xs
    (* | _ => (nil , nil) *)
  end.

