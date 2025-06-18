(* Compiles with Rocq 9.0.0 and Rocq-Elpi 2.5.2
   To compile: rocq compile Defun.v
 *)

From elpi Require Import elpi.


(* Uncomment the following line to print debug information *)
(* Elpi Debug "DEBUG_TRUE". *)


Elpi Command Defun.
Elpi Accumulate lp:{{

      %% For debugging
      pred ppctx.
      ppctx :- declare_constraint ppctx _.
      constraint ppctx copy {
        rule \ (G ?- ppctx) | (print "ctx is" G "\n") <=> true.
      }

      pred debug_pred i:string, i: option term.
      :if "DEBUG_TRUE"
      debug_pred S none :- coq.say S "\n", fail.
      :if "DEBUG_TRUE"
      debug_pred S (some T) :- coq.say S T "\n", fail.
      debug_pred _ _.


      %% Auxiliary non-optimal function to convert an int into a string
      pred int->string i:int, o:string.
      int->string 0 "I" :- !.
      int->string I S :- !,
        I1 is I - 1,
        int->string I1 S1,
        S is "I" ^ S1.


      %% Auxiliary functions to abstract over a list of variables
      pred add_prods i:list (pair term term), i:term, o:term.
      pred add_lams  i:list (pair term term), i:term, o:term.

      add_prods [] U1 U2 :- !, copy U1 U2.
      add_prods [(pr V T) | Vars] U (prod `_` T F) :- !,
        pi x\ decl x `_` T => (copy V x => (
          add_prods Vars U (F x)
        )).

      add_lams [] U1 U2 :- !, copy U1 U2.
      add_lams [(pr V T) | Vars] U (fun `_` T F) :- !,
        pi x\ decl x `_` T => (copy V x => (
          add_lams Vars U (F x)
        )).


      %% Auxiliary function to map over lists of pairs
      pred map_fst i:list (pair term (pair term term)), o:list term.
      map_fst [] [].
      map_fst [(pr A _) | L1] [A | L2] :- map_fst L1 L2.

      pred map_snd1 i:list (pair term (pair term term)), o:list (pair term term).
      map_snd1 [] [].
      map_snd1 [(pr A (pr B _)) | L1] [(pr A B) | L2] :- map_snd1 L1 L2.

      pred map_snd2 i:list (pair term (pair term term)), o:list (pair term term).
      map_snd2 [] [].
      map_snd2 [(pr A (pr _ B)) | L1] [(pr A B) | L2] :- map_snd2 L1 L2.


      %% Auxiliary function to reverse a list of constructors
      pred rev_acc i:list constructor, i:list constructor, o:list constructor.
      pred rev i:list constructor, o:list constructor.
      rev_acc L1 L2 L3 :- L1 = [], L2 = L3.
      rev_acc L1 L2 L3 :- L1 = [A | L], rev_acc L [A | L2] L3.
      rev L1 L2 :- rev_acc L1 [] L2.


      %% Auxiliary function to take the nth element of a constructor list
      pred list_nth i:int, i:list constructor, o:constructor.
      list_nth I L R :-
        L = [A | _],
        I = 0,
        R = A.
      list_nth I L R :-
        L = [_ | L1],
        I1 is I - 1,
        list_nth I1 L1 R.


      %% Defunctionalizing a type
      pred defun_type
        i:term,    % type to be removed
        i:term,    % global inductive constant
        i:term,    % type to defunctionalize
        o:term.    % resulting type

      % Particular Case 1: replace T₀ with IndSymGlob
      defun_type T0 IndSymGlob (prod N T0 F1 as TT) (prod N IndSymGlob F2) :- !,
        debug_pred "Calling defun_type 1 on" (some TT),
        pi x1\ decl x1 N T0 => (pi x2\ decl x2 N IndSymGlob => (copy x1 x2 => (
          defun_type T0 IndSymGlob (F1 x1) (F2 x2)))).

      % Simple traversals of a type
      defun_type T0 IndSymGlob (prod N T F1 as TT) (prod N T F2) :- !,
        debug_pred "Calling defun_type 2 on" (some TT),
        pi x\ decl x N T => defun_type T0 IndSymGlob (F1 x) (F2 x).
      defun_type T0 IndSymGlob (fun N T F1 as TT) (fun N T F2) :- !,
        debug_pred "Calling defun_type 3 on" (some TT),
        pi x\ decl x N T => defun_type T0 IndSymGlob (F1 x) (F2 x).
      defun_type _ _ T1 T2 :-
        debug_pred "Calling defun_type 4 on" (some T1),
        copy T1 T2, !.
      defun_type _ _ T _ :-
        debug_pred "Calling defun_type 5 on" (some T),
        coq.error "Failure in defun_type".


      %% Defunctionalizing a term, computing [apply] and the inductive type at
      %% the same time
      pred defun_term
        i:int,                                % temporary input arg to generate fresh
                                              %   constructor names (to be removed)
        o:int,                                % temporary output arg to generate fresh
                                              %   constructor names (to be removed)
        i:list (pair term (pair term term)),  % list of variables to put in the closure
        i:option term,                        % name of the higher-order function
                                              %   (to be replaced by a call to [apply])
        i:option term,                        % name of the reified first-order function
        i:term,                               % type to remove
        i:term,                               % term to defunctionalize
        o:term,                               % result
        i:term,                               % global [apply] constant
        i:term,                               % local [apply] symbol (for fixpoint definition)
        i:list term,                          % input list of patterns for [apply]
        o:list term,                          % output list of patterns for [apply]
        i:term,                               % global inductive constant
        i:string,                             % base name for the inductive constructor names
        i:list constructor,                   % global list of the inductive constructor names
        i:term,                               % local inductive symbol
                                              %   (for inductive declaration)
        i:list indc-decl,                     % input list of constructors for the inductive
        o:list indc-decl.                     % output list of constructors for the inductive

      pred defun_term_map                     % map defun_term to a list of terms (same parameters)
        i:int,
        o:int,
        i:list (pair term (pair term term)),
        i:option term,
        i:option term,
        i:term,
        i:list term,
        o:list term,
        i:term,
        i:term,
        i:list term,
        o:list term,
        i:term,
        i:string,
        i:list constructor,
        i:term,
        i:list indc-decl,
        o:list indc-decl.

      % Particular Case 2: for `λ(f:T₀). t₁` (represented by `fun N T0 F1`),
      %   remember `f` (represented by `some x2`)
      defun_term I1 I2 Vars _ _ T0 (fun N T0 F1 as UU) (fun N IndSymGlob F2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 01 on" (some UU),
        pi x1\ decl x1 N T0 => (pi x2\ decl x2 N IndSymGlob => (copy x1 x2 => (
          defun_term I1 I2 [(pr x2 (pr IndSymGlob IndSym)) | Vars] (some x1) (some x2) T0 (F1 x1) (F2 x2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2))).

      % Particular Case 3: replace `f @ t₂` (represented by `app [Y1 | L1]`)
      %   by `apply0 @ f @ t₂` (represented by `app [AppSym, Y2 | L2]`)
      % We are in the subcase where `apply0` (represented by AppSym) is in scope
      %   (the recursive call is used to define a pattern of `apply`)
      defun_term I1 I2 Vars (some Y1 as X1) (some Y2 as X2) T0 (app [Y1 | L1] as UU) (app [AppSym, Y2 | L2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,  %% Case where AppSym is in scope: body of [apply] fixpoint
        debug_pred "Calling defun_term 02a on" (some UU),
        defun_term_map I1 I2 Vars X1 X2 T0 L1 L2 AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2.

      % Particular Case 3: replace `f @ t₂` (represented by `app [Y1 | L1]`)
      %   by `apply @ f @ t₂` (represented by `app [AppSymGlob, Y2 | L2]`)
      % We are in the subcase where `apply0` (represented by AppSym) is *not* in scope
      %   (the recursive call is used to define `tₒᵤₜ`)
      defun_term I1 I2 Vars (some Y1 as X1) (some Y2 as X2) T0 (app [Y1 | L1] as UU) (app [AppSymGlob, Y2 | L2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,  %% Case where AppSym is not in scope: the global constant [apply] is used
        debug_pred "Calling defun_term 02b on" (some UU),
        defun_term_map I1 I2 Vars X1 X2 T0 L1 L2 AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2.

      % Particular Case 4: use `Vars` to define a new constructor (called `K`),
      %   replace `h` (represented by `A1`) with this new constructor
      %   (represented by `global (indc KGlob)`), and make a recursive call of
      %   the algorithm on `h` to define the corresponding pattern for `apply`
      %   (represented by `A2`)
      defun_term I1 I2 Vars X1 X2 T0 (app [F1, A1] as UU) (app [F2, app [(global (indc KGlob)) | Vs]]) AppSymGlob AppSym App1 [A2 | App2] IndSymGlob IndConsName IndConsGlob IndSym Ind1 [K | Ind2] :-
        coq.typecheck F1 (prod _ T0 _) ok, !,
        debug_pred "Calling defun_term 03 on" (some UU),
        defun_term I1 I3 Vars X1 X2 T0 F1 F2 AppSymGlob AppSym App1 App3 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind3,
        defun_term I3 I4 Vars X1 X2 T0 A1 A3 AppSymGlob AppSym App3 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind3 Ind2,
        I2 is I4 + 1,
        map_snd1 Vars Vars1,
        add_lams Vars1 A3 A2, !,
        map_fst Vars Vs,
        int->string I4 O,
        KId is IndConsName ^ O,
        map_snd2 Vars Vars2,
        add_prods Vars2 IndSym Ar,
        K = constructor KId (arity Ar),
        rev IndConsGlob IndConsGlob2,
        list_nth I4 IndConsGlob2 KGlob.

      % Simple traversals of a term
      defun_term _ _ _    _ _ _ (app [] as UU) (app []) _ _ App App _ _ _ _ Ind Ind :- !,
        debug_pred "Calling defun_term 04 on" (some UU).
      defun_term I1 I2 Vars X1 X2 T0 (app [A1] as UU) (app [A2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 05 on" (some UU),
        defun_term I1 I2 Vars X1 X2 T0 A1 A2 AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2.
      defun_term I1 I2 Vars X1 X2 T0 (app [F1, A1] as UU) (app [F2, A2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 06 on" (some UU),
        defun_term I1 I3 Vars X1 X2 T0 F1 F2 AppSymGlob AppSym App1 App3 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind3,
        defun_term I3 I2 Vars X1 X2 T0 A1 A2 AppSymGlob AppSym App3 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind3 Ind2.
      defun_term I1 I2 Vars X1 X2 T0 (app [F1, A1 | L1] as UU) (app [F2, A2 | L2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 07 on" (some UU),
        defun_term I1 I2 Vars X1 X2 T0 (app [(app [F1, A1]) | L1]) (app [(app [F2, A2]) | L2]) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2.
      defun_term I1 I2 Vars X1 X2 T0 (fix N Rno Ty1 F1 as UU) (fix N Rno Ty2 F2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 08 on" (some UU),
        defun_type T0 IndSymGlob Ty1 Ty2,
        pi x1\ decl x1 N Ty1 => (pi x2\ decl x2 N Ty2 => (copy x1 x2 => (
        defun_term I1 I2 Vars X1 X2 T0 (F1 x1) (F2 x2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2   %% Do not bind fix in the closure
      ))).
      defun_term I1 I2 Vars X1 X2 T0 (match T1 Rty1 B1 as UU) (match T2 Rty2 B2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 09 on" (some UU),
        defun_term I1 I3 Vars X1 X2 T0 T1 T2 AppSymGlob AppSym App1 App3 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind3,
        defun_type T0 IndSymGlob Rty1 Rty2,
        defun_term_map I3 I2 Vars X1 X2 T0 B1 B2 AppSymGlob AppSym App3 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind3 Ind2.
      defun_term I1 I2 Vars X1 X2 T0 (fun N T F1 as UU) (fun N T F2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 10 on" (some UU),
        pi x\ (decl x N T => (
          defun_term I1 I2 [(pr x (pr T T)) | Vars] X1 X2 T0 (F1 x) (F2 x) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2
        )).
      defun_term I1 I2 Vars X1 X2 T0 (let N T1 B1 F1 as UU) (let N T2 B2 F2) AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :- !,
        debug_pred "Calling defun_term 11 on" (some UU),
        defun_type T0 IndSymGlob T1 T2,
        defun_term I1 I3 Vars X1 X2 T0 B1 B2 AppSymGlob AppSym App1 App3 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind3,
        pi x1\ decl x1 N T1 => (pi x2\ decl x2 N T2 => (copy x1 x2 => (
          defun_term I3 I2 Vars X1 X2 T0 (F1 x1) (F2 x2) AppSymGlob AppSym App3 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind3 Ind2
        ))).
      defun_term I I _ _ _ _ U1 U2 _ _ App App _ _ _ _ Ind Ind :-
        debug_pred "Calling defun_term 12 on" (some U1),
        copy U1 U2, !.
      defun_term _ _ _ _ _ _ U _ _ _ _ _ _ _ _ _ _ _ :-
        debug_pred "Calling defun_term 13 on" (some U),
        coq.error "Failure in defun_term".

      defun_term_map I I _ _ _ _ [] [] _ _ App App _ _ _ _ Ind Ind.
      defun_term_map I1 I2 Vars X1 X2 T0 [U1 | Us1] [U2 | Us2] AppSymGlob AppSym App1 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind2 :-
        defun_term I1 I3 Vars X1 X2 T0 U1 U2 AppSymGlob AppSym App1 App3 IndSymGlob IndConsName IndConsGlob IndSym Ind1 Ind3,
        defun_term_map I3 I2 Vars X1 X2 T0 Us1 Us2 AppSymGlob AppSym App3 App2 IndSymGlob IndConsName IndConsGlob IndSym Ind3 Ind2.


      %% Main defunctionalizing function
      pred defun
        i:term,              % type to remove
        i:term,              % term to defunctionalize
        o:term,              % result
        i:term,              % global constant [apply]
        o:term,              % body of [apply]
        i:string,            % name of the inductive type
        i:term,              % global constant for the inductive type
        i:list constructor,  % global list of inductive constructor names
        o:indt-decl.         % body of the inductive type
      defun T0 U1 U2 AppSymGlob (fix `apply0` 0 (prod `k` IndSymGlob (x\ T0)) F) Ind IndSymGlob IndConsGlob (inductive Ind tt (arity T) I) :-
        T = {{ Type }},
        (pi appsym\ ((decl appsym `apply0` (prod `k` IndSymGlob (x\ T0))) => (pi indsym\ ((decl indsym `cont` T) => (
          defun_term 0 _ [] none none T0 U1 U2 AppSymGlob appsym [] (App2 appsym) IndSymGlob Ind IndConsGlob indsym [] (Ind2 indsym),
          F appsym = fun `k` IndSymGlob (z\ match z (fun `k` IndSymGlob (x\ T0)) (App2 appsym)),
          I indsym = Ind2 indsym
        ))))).


      %% Entry point
      main [trm T, trm Ty, str Defun, str Apply, str Ind] :- !,
        std.assert-ok! (coq.elaborate-skeleton T _ T1) "illtyped arg",
        std.assert-ok! (coq.elaborate-skeleton Ty _ Ty1) "illtyped arg",
        defun Ty T1 T2 AppSymGlob App2 Ind IndSymGlob IndConsGlob Ind2,
        std.assert-ok! (coq.typecheck-indt-decl Ind2) "invalid resulting data",
        coq.env.add-indt Ind2 Ind0,
        IndSymGlob = global (indt Ind0),
        std.assert! (coq.locate Ind (indt GR)) "error when defining the inductive type",
        coq.env.indt GR _ _ _ _ IndConsGlob _,
        std.assert-ok! (coq.elaborate-skeleton App2 _ App3) "invalid resulting apply",
        coq.env.add-const Apply App3 _ _ Apply0,
        AppSymGlob = global (const Apply0),
        std.assert-ok! (coq.elaborate-skeleton T2 _ T3) "invalid result",
        coq.env.add-const Defun T3 _ _ _.
      main [trm _, trm _, str _, str _, _] :- coq.error "The 5th parameter should be the name of the data type".
      main [trm _, trm _, str _, _, _] :- coq.error "The 4th parameter should be the name of the `apply` function".
      main [trm _, trm _, _, _, _] :- coq.error "The 3rd parameter should be the name of the defunctionalized term".
      main [trm _, _, _, _, _] :- coq.error "The 2nd parameter should be the type to remove".
      main [_, _, _, _, _] :- coq.error "The 1st parameter should be the term to defunctionalize".
      main _ :- coq.error "Wrong number of arguments (usage: Defun ([term to defunctionalize]) ([type to remove]) [name of the defunctionalized term] [name of the `apply` function] [name of the data type])".
}}.

Elpi Export Defun.



(* Example: defunctionalization of the factorial function written with a
   continuation *)
Definition natToNat := nat -> nat.
Defun (let fact' :=
    fix fact' n (k:natToNat) :=
      match n with
      | 0 => k 1
      | S p => fact' p (fun x => k (n * x))
      end
  in
  let fact := fun n => fact' n (fun x => x) in
  fact) (natToNat) fact apply cont.
Print fact.
Print apply.
Print cont.


(* Example: variant on the binding over the continuation *)
Defun (let fact' :=
    fix fact' n : natToNat -> nat :=
      match n with
      | 0 => fun k => k 1
      | S p => fun k => fact' p (fun x => k (n * x))
      end
  in
  let fact := fun n => fact' n (fun x => x) in
  fact) (natToNat) fact' apply' cont'.
Print fact'.
Print apply'.
Print cont'.


(* Example: append of two lists with a continuation *)
Require Import List.
Section Append.
  Variable A : Type.

  Definition listAToListA := list A -> list A.

  Defun (
    let append' :=
      fix append' l1 l2 (k:listAToListA) :=
        match l1 with
        | nil => k l2
        | x::xs => append' xs l2 (fun r => k (x::r))
        end
    in
    let append := fun l1 l2 => append' l1 l2 (fun r => r) in
    append) (listAToListA) app applyApp contApp.

  Print app.
  Print applyApp.
  Print contApp.
End Append.
