%% -*- mode: prolog; coding: utf-8 -*-

%% GNU Prolog défini `new_atom`, mais SWI Prolog l'appelle `gensym`.
genatom(X, A) :-
    (predicate_property(new_atom/2, built_in);    % Older GNU Prolog
     predicate_property(new_atom(_,_), built_in)) % Newer GNU Prolog
    -> new_atom(X, A);
    gensym(X, A).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Description de la syntaxe des termes %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% wf(+E)
%% Vérifie que E est une expression syntaxiquement correcte.
%% Cette règle est inutile en soit, elle ne sert qu'à documenter pour
%% vous la forme des termes du langage μPTS.

%% D'abord les termes du langage interne.
wf(X) :- identifier(X); integer(X); float(X).       %Une variable ou un nombre.
wf(fun(X, T, E)) :- identifier(X), wf(T), wf(E).    %Une fonction.
wf(app(E1, E2)) :- wf(E1), wf(E2).                  %Un appel de fonction.
wf(arw(X, T1, T2)) :- identifier(X), wf(T1), wf(T2). %Le type d'une fonction.
wf(let(X, T, E1, E2)) :- identifier(X), wf(T), wf(E1), wf(E2). %Def locale.

%% Puis les éléments additionnels acceptés dans le langage surface.
wf(forall(X, T, B)) :- identifier(X), wf(T), wf(B). %Type d'une fonc. implicite
wf(fun(X, B)) :- identifier(X), wf(B).
wf(let(X, E1, E2)) :- identifier(X), wf(E1), wf(E2).
wf(let(Decls, E)) :- wf_decls(Decls), wf(E).
wf((T1 -> T2)) :- wf(T1), wf(T2).
wf(forall(X, B)) :- (identifier(X); wf_ids(X)), wf(B).
wf((E : T)) :- wf(E), wf(T).
wf(E) :- E =.. [Head|Tail], identifier(Head), wf_exps(Tail).
wf(X) :- var(X).    %Une métavariable, utilisée pendant l'inférence de type.

%% identifier(+X)
%% Vérifie que X est un identificateur valide.
identifier(X) :-
    atom(X),
    \+ member(X, [fun, app, arw, forall, (->), (:), let, [], (.)]).

wf_exps([]).
wf_exps([E|Es]) :- wf(E), wf_exps(Es).
wf_ids([]).
wf_ids([X|Xs]) :- identifier(X), wf_ids(Xs).
wf_decls([]).
wf_decls([X = E|Decls]) :-
    wf_decls(Decls), wf(E),
    (X = (X1 : T) -> wf(T), X1 =.. Ids, wf_ids(Ids);
     X =.. [F|Args], identifier(F), wf_args(Args)).
wf_args([]).
wf_args([X:T|Args]) :- wf_args(Args), identifier(X), wf(T).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Manipulation du langage interne %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Occasionnellement pendant l'inférence de types, il se peut qu'une
%% métavariable apparaisse dans un terme du langage interne.  Donc les
%% prédicats ci-dessous font souvent attention à tester le cas `var(MV)`
%% (accompagné d'un `cut`) pour veiller à ne pas instancier cette
%% métavariable par inadvertance, parce que cela mène sinon très vite à des
%% boucles sans fin difficiles à déboguer.

%% subst(+Env, +X, +V, +Ei, -Eo)
%% Remplace X par V dans Ei. V et Ei sont des expressions du langage interne.
%% Les variables qui peuvent apparaître libres dans V (et peuvent aussi
%% apparaître dans Ei) doivent toutes être incluses dans l'environnement Env.
%% Cette fonction évite la capture de nom, e.g.
%%
%%     subst(Env, x, y, fun(y,int,x+y), R)
%%
%% ne doit pas renvoyer `R = fun(y,int,y+y)` mais `R = fun(y1,int,y+y1)`.
subst(_, _, _, MV, Eo) :-
    %% Si MV est un terme non-instancié (i.e. une métavariable), la 
    %% substitution ne peut pas encore se faire.  Dans certains cas, on
    %% pourrait renvoyer app(fun(X,Y),V), mais en général c'est problématique.
    %% Donc on impose ici la contrainte que les metavars ne peuvent pas
    %% faire référence à X.
    %% Le faire vraiment correctement est plus difficile.
    var(MV), !, Eo = MV.
subst(_, X, V, X, V).
subst(_, _, _, E, E) :- identifier(E); integer(E).
subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)) :-
    subst(Env, X, V, Ti, To),
    (X = Y ->
         %% Si X est égal à Y, X est caché, donc aucune substitution n'a lieu!
         Y1 = Y, Bo = Bi;
     (member((Y : _), Env) ->
          %% Si Y apparait dans Env, il peut apparaître dans V, donc on doit
          %% le renommer pour éviter une possible capture.
          genatom(Y, Y1),
          subst([], Y, Y1, Bi, Bi1);
      %% Cas "normal" où il n'y a pas de conflit de nom.
      Y1 = Y, Bi1 = Bi),
     %% Applique la substitution sur le corps de la fonction.
     subst(Env, X, V, Bi1, Bo)).
subst(Env, X, V, arw(Y, Ti, Bi), arw(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, forall(Y, Ti, Bi), forall(Y1, To, Bo)) :-
    subst(Env, X, V, fun(Y, Ti, Bi), fun(Y1, To, Bo)).
subst(Env, X, V, app(E1i, E2i), app(E1o, E2o)) :-
    subst(Env, X, V, E1i, E1o), subst(Env, X, V, E2i, E2o).


%% apply(+Env, +F, +Arg, -E)
%% Les règles d'évaluations primitives. Env donne le types des variables
%% libres qui peuvent apparaître.
apply(Env, fun(X, _, B), Arg, E) :- \+ var(B), subst(Env, X, Arg, B, E).
apply(_,   app(+, N1), N2, N) :- integer(N1), integer(N2), N is N1 + N2.
apply(_,   app(-, N1), N2, N) :- integer(N1), integer(N2), N is N1 - N2.


%% normalize(+Env, +Ei, -Eo)
%% Applique toutes les réductions possibles sur Ei et tous ses sous-termes.
%% Utilisé pour tester si deux types sont équivalents.
normalize(_, MV, Eo) :- var(MV), !, Eo = MV.
normalize(_, V, V) :- (integer(V); float(V); identifier(V)).
normalize(Env, fun(X, T, B), fun(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn),
    normalize([X:T|Env], B, Bn).
normalize(Env, arw(X, T, B), arw(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn),
    normalize([X:T|Env], B, Bn).
normalize(Env, forall(X, T, B), forall(X, Tn, Bn)) :-
    normalize([X:T|Env], T, Tn),
    normalize([X:T|Env], B, Bn).
normalize(Env, app(E1, E2), En) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    (apply(Env, E1n, E2n, E) ->
        normalize(Env, E, En);
        En = app(E1n, E2n)).

%% equal(+Env, +T1, +T2)
%% Vérifie que deux expressions sont égales.
%% Utilisé pour vérifier l'égalité des types au niveau du langage interne, où
%% `forall` et `arw` sont équivalents.
equal(_, E, E).
equal(Env, forall(X1, T1, E1), E2) :- equal(Env, arw(X1, T1, E1), E2).
equal(Env, E2, forall(X1, T1, E1)) :- equal(Env, E2, arw(X1, T1, E1)).
equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)) :-
    equal(Env, T1, T2),
    Env1 = [X1:T1|Env],
    (X1 = X2 ->
         E3 = E2;
     %% Si X1 et X2 sont différents, renomme X2 dans E2!
     subst(Env1, X2, X1, E2, E3)),
    equal(Env1, E1, E3).
equal(Env, arw(X1, T1, E1), arw(X2, T2, E2)) :-
    equal(Env, fun(X1, T1, E1), fun(X2, T2, E2)).
equal(Env, E1, E2) :-
    normalize(Env, E1, E1n),
    normalize(Env, E2, E2n),
    ((E1 = E1n, E2 = E2n) ->
         %% There was nothing to normalize :-(
         fail;
     equal(Env, E1n, E2n) -> true).
        

%% verify(+Env, +E, +T)
%% Vérifie que E a type T dans le contexte Env.
%% E est une expression du langage interne (i.e. déjà élaborée).
%% Elle ne devrait pas contenir de métavariables.
verify(Env, E, T) :-
    verify1(Env, E, T1) ->
        (equal(Env, T, T1) -> true;
         write(user_error, not_equal(T, T1)), nl(user_error), fail);
    write(user_error, verify_failure(E)), nl(user_error), fail.


%% verify1(+Env, +E, -T)
%% Calcule le type de E dans Env.
verify1(_, MV, _) :- var(MV), !, fail.
verify1(_, N, int) :- integer(N).
verify1(_, N, float) :- float(N).
verify1(Env, X, T) :-
    %% `member(X:T, Env)` risquerait de trouver dans Env un autre X que le
    %% plus proche, au cas où il y a plusieurs X dans l'environnement.
    atom(X), (member(X:T1, Env) -> T = T1; fail).
verify1(Env, fun(X, T1, E), forall(X, T1, T2)) :-
    verify(Env, T1, type),
    verify1([X:T1|Env], E, T2).
verify1(Env, app(F, A), T2) :-
    verify(Env, F, arw(X, T1, T3)),
    verify(Env, A, T1),
    subst(Env, X, A, T3, T2).
verify1(Env, arw(X, T1, T2), type) :-
    verify(Env, T1, type),
    verify([X:T1|Env], T2, type).
verify1(Env, forall(X, T1, T2), T) :-
    verify1(Env, arw(X, T1, T2), T).
verify1(Env, let(X, T, E1, E2), Tret) :-
    verify(Env, T, type),
    Env1 = [X:T|Env],
    verify(Env1, E1, T),
    verify1(Env1, E2, Tret).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Élaboration du langage surface vers le langage interne %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% expand(+Ei, -Eo)
%% Remplace un élement de sucre syntaxique dans Ei, donnant Eo.
%% Ne renvoie jamais un Eo égal à Ei.
expand(MV, _) :- var(MV), !, fail.
expand(T1 -> T2, arw(X, T1, T2)) :- genatom('dummy_', X).

expand(forall(X, B), F) :-
    (X = [T | TS], TS \= [] ->
            F = forall(T, _, forall(TS, B));
            (X = [A] ->
                F = forall(A, _, B);
                F = forall(X, _, B))).

expand(let([D = V | DS], B), LX) :-
    (D = (X : T) ->
        (functor(X, X, 0) ->
            (DS = [] ->
                LX = let(X, T, V, B);
                LX = let(X, T, V, let(DS, B)));
            X =.. [N | AS],
            convertFun(AS, V, F),
            (DS = [] ->
                LX = let(N, T, F, B);
                LX = let(N, T, F, let(DS, B))));
        D =.. [N | AS],
        (AS = [] ->
            (DS = [] ->
                LX = let(N, V, B);
                LX = let(N, V, let(DS, B)));
            convertFun(AS, V, F),
            (DS = [] ->
                LX = let(N, F, B);
                LX = let(N, F, let(DS,B))))).

expand(Fcall, App) :-
    Fcall =.. [N | AS],
    \+ member(N, [fun, app, arw, forall, (->), (:), let, [], (.)]),
    length(AS, L),
    L \= 0,
    functor(Fcall, N, L),
    append([N], AS, F),
    curryCall(F, App).

%% convertFun(+AS, +V, -F)
convertFun([], V, V).
convertFun([A | AS], V, F) :-
    convertFun(AS, V, B),
    (A = (X : T) ->
        F = fun(X, T, B);
        F = fun(A, B)).

%% curryCall(+functor, -app(F, A))
curryCall([F, A], app(F, A)).
curryCall(F ,app(App, A)) :-
    last(F, A),
    append(AS, [A], F),
    curryCall(AS, App).

% Helper method to construct `let`
% convertlet(X = E, NA, ET, EF) :-
%     (X = (X1 : T) ->
%         NA = X1,
%         expand(T,ET),
%         convertfun1(NA,E,ET,EF);
%         X =.. [NA|Args],
%         convertfun(Args,E,EF),
%         EF =.. [_|Args1],
%         extracttype(Args1,TT),
%         TT =..Args2,
%         convertype(Args2,ET)).
% % Faut gérer le cas où on a plusieurs paramètres implicites.
% convertfun1(A,F,arw(_,T,XS),fun(EA,T,EXS)) :-
%         XS = arw(_,T1,T2), 
%         (F = fun(X,Y) ->
%             EA = A,
%             EXS = fun(X,T1,T2);
%             A =.. [EA|[Arg|[]]],
%             EXS = fun(Arg,T1,T2)).
% 
% %  % Extract type for let. Ex: fun(x,int,fun(y,int,x+y)) => (int->int)
% %  % Take advantage of list decomposition in Prolog.
% %  % fun(x,int,fun(y,int,x+y)) => [fun,x, int, fun(y,int,x+y)].
% % extracttype([_, T, F], (T-> (ET))) :-
% %      F =.. [_|[_|[B|[C|[]]]]],
% %      (C = fun(_,_,_) ->
% %          F =.. [_|Args],
% %          extracttype(Args,ET); ET = B).
% % 
% % %  Convert arrow notation. Ex: (E1->E2->E3) => arw(_,E1,arw(_,E2,E3))
% % %  Take advantage of list decompisition
% % %  (E1 -> E2 -> E3) => [->, E1,(E2->E3)].
% % %  (E1 -> E2) => [->,E1,E2].
% % %  Doesn't decompose "list(E1,E2)"
% % convertype([_|[T|[F|[]]]],arw(X,T,EF)) :-
% %     genatom("dummy_",X),
% %     F =.. [FF|Args],
% %     (Args = [] ->
% %         EF = FF;
% %         FF = list ->
% %             EF = F;
% %             F =.. TF,
% %             convertype(TF,EF)).
% 
% 
% expand((T1 -> T2), arw(X, T1, ET2)) :-
%     genatom('dummy_', X),
%     T2=..ST2,
%     length(ST2,Len),
%     (Len = 3, \+ member(list,ST2) -> convertype(ST2,ET2); ET2 = T2).
%
%  expand(forall([X|XS],B),arw(X,type,EB)) :- expand(forall(XS,B),EB).
%  expand(forall(A,B),arw(A,type,EB)) :- expand(B,EB).
% 
%  expand(forall(A,B,C),arw(A,EB,EC)) :- expand(B,EB),expand(C,EC).
% 
%  expand(arw(A,B,C),arw(A,EB,EC)) :-
%      expand(B,EB),expand(C,EC);
%      (B = _ -> EB = type, expand(C,EC); false).
% 
% expand((T1 -> T2), arw(X, T1, ET2)) :- genatom('dummy_', X),
%                                         T2=..ST2,
%                                         length(ST2,Len),
%                                         (Len = 3, \+ member(list,ST2) -> convertype(ST2,ET2); ET2 = T2).
% 
% expand(forall([X|XS],B),arw(X,type,EB)) :- expand(forall(XS,B),EB).
% expand(forall(A,B),arw(A,type,EB)) :- (B=list(_,_) -> EB = B; expand(B,EB)).
% 
% expand(forall(A,B,C),arw(A,EB,EC)) :- expand(B,EB),expand(C,EC).
% 
% expand(arw(A,B,C),arw(A,EB,EC)) :-
%      expand(B,EB),expand(C,EC);
%      (B = _ -> EB = type, expand(C,EC); false).
% 
% expand(let(A,B,C),let(A,ET,B,EC)) :-
%      expand(C,EC), B =.. [_|Args],
%      extracttype(Args,TT),
%      expand(TT,ET).
% 
% % % let sucre syntaxique
% % % NA: nom de variable, EF: Evaluated Function, EC: Evaluated corps, ET: Evaluated Type
% expand(let([X], C), let(NA,ET,EF,EC)) :-
%     convertlet(X,NA,ET,EF), expand(C,EC).
% 
% expand(let([X|XS],C),let(NA,ET,EF,EC)) :-
%         convertlet(X,NA,ET,EF),
%         expand(let(XS,C),EC).
% 
% 
% % expand(X,A) :- X =.. [F|Args], append([F],Args,EF), convertapp(EF,A).
% 
% convertapp([X|[XS|[]]],app(X,XS)).
% convertapp(X,app(EA,EX)) :- last(X,EX),append(TA,[EX],X),convertapp(TA,EA).
% 
% 
%
% 

%% !!!À COMPLÉTER!!!


%% coerce(+Env, +E1, +T1, +T2, -E2)
%% Transforme l'expression E1 (qui a type T1) en une expression E2 de type T2.
coerce(Env, E, T1, T2, E) :-
    T1 = T2;
    normalize(Env, T1, T1n),
    normalize(Env, T2, T2n),
    T1n = T2n.        %T1 = T2: rien à faire!

% Fig 2 - Règle 12
coerce(Env, E1, forall(X, _, E3), T, app(E1, E4)) :-
    subst(Env, X, E4, E3, T).

% Fig 2 - Règle 13
coerce(_, E1, int, float, app(int_to_float, E1)).

% Fig 2 - Règle 14
coerce(_, E1, int, bool, app(int_to_bool, E1)).

%% !!!À COMPLÉTER!!!

% rewrite(Env, Fa, Fb) :-
%     Fa =.. [N | As],
%     member((N : forall(X, T, B)), Env),
    

%% infer(+Env, +Ei, -Eo, -T)
%% Élabore Ei (dans un contexte Env) en Eo et infère son type T.
infer(_, MV, MV, _) :- var(MV), !.            %Une expression encore inconnue.
infer(Env, Ei, Eo, T) :- rewrite(Env, Ei, Ei1), expand(Ei1, Ei2), infer(Env, Ei2, Eo, T).
infer(_, X, X, int) :- integer(X).
infer(_, X, X, float) :- float(X).
infer(Env, (Ei : T), Eo, T1) :-
    check(Env, T, type, T1),
    check(Env, Ei, T1, Eo).

% Fig 2 - Règle 6
infer(Env, app(E1a, E2a), app(E1b, E2b), T) :-
    (member((E1a : forall(_, _, _)), Env) ->
        infer(Env, E1a, E1b, forall(X, E4, E5));
        infer(Env, E1a, E1b, arw(X, E4, E5))),
    check(Env, E2a, E4, E2b),
    subst(Env, X, E2b, E5, T).

% Fig 2 - Règle 4
infer(Env, arw(X, E1a, E2a), arw(X, E1b, E2b), type) :-
    check(Env, E1a, type, E1b),
    check([(X : E1b) | Env], E2a, type, E2b).

% Fig 2 - Règle 5
infer(Env, forall(X, E1a, E2a), forall(X, E1b, E2b), type) :-
    check(Env, E1a, type, E1b),
    check([(X : E1b) | Env], E2a, type, E2b).

% Fig 2 - Règle 2
infer(Env, fun(X, E1a, E2a), fun(X, E1b, E2b), arw(_, E1b, E3)) :-
    check(Env, E1a, type, E1b),
    infer([(X : E1b) | Env], E2a, E2b, E3).

% Fig 2 - Règle 7
infer(Env, let(X, E1a, E2a, E3a), let(X, E1b, E2b, E3b), E4) :-
    check(Env, E1a, type, E1b),
    check([(X : E1b) | Env], E2a, E1b, E2b),
    infer([(X : E1b) | Env], E3a, E3b, E4).

% Fig 2 - Règle 8
infer(Env, let(X, E2a, E3a), let(X, E1, E2b, E3b), E4) :-
    infer([(X : E1) | Env], E2a, E2b, E1),
    infer([(X : E1) | Env], E3a, E3b, E4).

% Fig 2 - Règle 1
infer(Env, X, X, T) :-
    member((X : T), Env).
%% !!!À COMPLÉTER!!!

%% check(+Env, +Ei, +T, -Eo)
%% Élabore Ei (dans un contexte Env) en Eo, en s'assurant que son type soit T.
check(_Env, MV, _, Eo) :-
    %% On ne fait pas l'effort de se souvenir du type des métavariables,
    %% donc on ne peut pas vérifier si MV a effectivement le type attendu.
    %% À la place, on accepte n'importe quel usage de métavariables, en
    %% espérant qu'elles sont utilisées correctement.  C'est généralement le
    %% cas de toute façon, et pour les cas restants on se repose sur le filet
    %% de sécurité qu'est `verify`.
    var(MV), !, Eo = MV.
check(Env, Ei, T, Eo) :-
    expand(Ei, Ei1),
    check(Env, Ei1, T, Eo).

% Fig 2 - Règle 10
check(Env, E1a, E3, E1b) :-
    infer(Env, E1a, E1b, E2),
    equal(Env, E2, E3).

% Fig 2 - Règle 11
check(Env, E1a, forall(X, E2, E3), E1b) :-
    check([(X : E2) | Env], E1a, E3, E1b).

% Fig 2 - Règle 3
check(Env, fun(X, E2a), arw(_, E1, E3), fun(X, E1, E2b)) :-
    check([(X : E1) | Env], E2a, E3, E2b).
%% !!!À COMPLÉTER!!!

%% Finalement, cas par défaut:
check(Env, Ei, T, Eo) :-
    infer(Env, Ei, Eo1, T1),
    (coerce(Env, Eo1, T1, T, Eo) -> true).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Environnement initial et tests %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


elaborate_env(Env, [], Env).
elaborate_env(Env, [X:Ti|Envi], Envo) :-
    check(Env, Ti, type, To) ->
        (verify(Env, To, type) ->
             elaborate_env([X:To|Env], Envi, Envo));
    write(user_error, 'FAILED_TO_ELABORATE'(Ti)), nl(user_error), !, fail.

initenv(Env) :-
    elaborate_env(
        [type : type],
        [int : type,
         float : type,
         bool : type,
         int_to_float : (int -> float),
         int_to_bool : (int -> bool),
         list : (type -> int -> type),
         (+) : (int -> int -> int),
         (-) : (int -> int -> int),
         (*) : (int -> int -> int),
         (/) : (float -> float -> float),
         (<) : (float -> float -> int),
         if : forall(t, (bool -> t -> t -> t)),
         nil :  forall(t, list(t, 0)),
         cons : forall([t,n],(t -> list(t, n) -> list(t, n + 1)))],
        Env).
% infer([type : type,int : type,float : type,bool : type,int_to_float : arw(dummy_16, int, float),int_to_bool : arw(dummy_17, int, bool),list : arw(dummy_18, type, arw(dummy_19, int, type)),(+) : arw(dummy_1, int, arw(dummy_2, int, int)),(-) : arw(dummy_3, int, arw(dummy_4, int, int)),(*) : arw(dummy_5, int, arw(dummy_6, int, int)),(/) : arw(dummy_7, float, arw(dummy_8, float, float)),(<) : arw(dummy_9, float, arw(dummy_10, float, int)),if : forall(t, type, arw(dummy_11, bool, arw(dummy_12, t, arw(dummy_13, t, t)))),nil : forall(t, type, app(app(list, t), 0)),cons : forall(t, type, (forall(n, int, arw(dummy_14, t, arw(dummy_15, app(app(list,t), n), app(app(list,t), app(app(+, n), 1)))))))], cons(13, nil), E, T).

% check([add:arw(dummy_1126, int, arw(dummy_1127, int, int)),type : type,int : type,float : type,bool : type,int_to_float : arw(dummy_16, int, float),int_to_bool : arw(dummy_17, int, bool),list : arw(dummy_18, type, arw(dummy_19, int, type)),(+) : arw(dummy_1, int, arw(dummy_2, int, int)),(-) : arw(dummy_3, int, arw(dummy_4, int, int)),(*) : arw(dummy_5, int, arw(dummy_6, int, int)),(/) : arw(dummy_7, float, arw(dummy_8, float, float)),(<) : arw(dummy_9, float, arw(dummy_10, float, int)),if : forall(t, type, arw(dummy_11, bool, arw(dummy_12, t, arw(dummy_13, t, t)))),nil : forall(t, type, app(app(list, t), 0)),cons : forall(t, type, (forall(n, int, arw(dummy_14, t, arw(dummy_15, app(app(list,t), n), app(app(list,t), app(app(+, n), 1)))))))], fun(x, fun(y, x + y)), arw(dummy_1126, int, arw(dummy_1127, int, int)), X).

%% Quelques expressions pour nos tests.
% sample(1 + 2).
% sample(1 / 2).
sample(let([identity(x) : (forall(t, (t -> t))) = x], identity(3))).
sample(nil(int)).
sample(if(1 < 2, 1, 2)). % Test fails here
sample(cons(13,nil)).
sample(cons(1.0, cons(2.0, nil))).
sample(let([fact(n:int) = if(n < 2, 1, n * fact(n - 1))],fact(44))).
sample(let([fact(n) : (int -> int) = if(n < 2, 1, n * fact(n - 1))],fact(45))).
sample(let(
    [list1 : forall(a, (a -> list(a, 1))) = fun(x, cons(x, nil))],list1(42))).
sample(let(
    [list1(x) : forall(a, (a -> list(a, 1))) = cons(x, nil)],list1(43))).
    
%% L'argument 'n' ne peut être que 0, ici, et on peut l'inférer!
sample(let(
    [pushn(n,l) : arw(n, _, (list(int,n) -> list(int,n + 1))) = cons(n,l)],
    pushn(_,nil))).

%% Roule le test sur une expression.
test_sample(Env, E) :-
    infer(Env, E, Eo, T) ->
        normalize(Env, T, T1),
        write(user_error, inferred(E, T1)), nl(user_error),
        write(user_error, verifying(Eo)), nl(user_error),
        (verify(Env, Eo, T) ->
             write(user_error, 'VERIFIED!!'), nl(user_error);
         write(user_error, 'FAILED_TO_VERIFY'(Eo)), nl(user_error));
    write(user_error, 'FAILED_TO_INFER'(E)), nl(user_error).

%% Roule le test sur chacune des expressions de `sample`.
test_samples :-
    initenv(Env), sample(E), test_sample(Env, E).
