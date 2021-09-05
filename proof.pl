:- use_module(library(clpfd)).

% Language:
% e + e, e - e, e * e, integer, x
% x := e
% skip
% if e { e } else { e }
% while e { e }
% s ; s

:- dynamic proof/1.
:- discontiguous proof/1.
:- discontiguous proof_example/1.

% ========================
% First order logic
% ========================

proof(rule(assm, [], proves(S, P))) :- member(P, S).

proof(rule(trueI, [], proves(_S, true))).

proof(rule(falseE, [Prf], proves(S, _))) :-
    proof_of(Prf, S, false).

proof(rule(notI, [Prf], proves(S, not(A)))) :-
    proof_of(Prf, [A|S], false).
proof(rule(notE, [Prf, NotPrf], proves(S, false))) :-
    proof_of(Prf, S, A),
    proof_of(NotPrf, S, not(A)).

proof(rule(orIL, [APrf], proves(S, A\/_B))) :-
    proof_of(APrf, S, A).
proof(rule(orIR, [BPrf], proves(S, _A\/B))) :-
    proof_of(BPrf, S, B).
proof(rule(orE, [OrPrf, FromA, FromB], proves(S, C))) :-
    proof_of(OrPrf, S, A\/B),
    proof_of(FromA, [A|S], C),
    proof_of(FromB, [B|S], C).

proof(rule(andI, [APrf, BPrf], proves(S, A/\B))) :-
    proof_of(APrf, S, A),
    proof_of(BPrf, S, B).
proof(rule(andEL, [Prf], proves(S, A))) :-
    proof_of(Prf, S, A/\_).
proof(rule(andER, [Prf], proves(S, B))) :-
    proof_of(Prf, S, _/\B).

proof(rule(impI, [Prf], proves(S, A->B))) :-
    proof_of(Prf, [A|S], B).
proof(rule(impE, [ImpPrf, HypPrf], proves(S, B))) :-
    proof_of(ImpPrf, S, A->B),
    proof_of(HypPrf, S, A).

proof(rule(allI, [Prf], proves(S, forall(X, P)))) :-
    proof_of(Prf, S, Q),
    substitute(X, Y, P, Q),
    fresh([forall(X, P)|S], Y).
proof(rule(allE, [AllPrf], proves(S, Q))) :-
    proof_of(AllPrf, S, forall(X, P)),
    substitute(X, _, P, Q).

proof(rule(exI, [Prf], proves(S, exists(X, P)))) :-
    % There must be some such expression E so we can prove the property holds,
    % but we don't care what it is.
    substitute(X, _E, P, Q),
    proof_of(Prf, S, Q).
proof(rule(exE, [ExPrf, UsePrf], proves(S, C))) :-
    proof_of(ExPrf, S, exists(X, P)),
    proof_of(UsePrf, [Q|S], C),
    substitute(X, Y, P, Q),
    fresh([exists(X, P)|S], Y).

% ========================
% Hoare Logic
% ========================

proof(rule(skip, [], P-skip-P)).

proof(rule(assign, [], P-(X:=E)-Q)) :-
    substitute(X, E, Q, P).

proof(rule(seq, [S1Prf, S2Prf], P-(S1;S2)-Q)) :-
    proof_of(S1Prf, P-S1-R),
    proof_of(S2Prf, R-S2-Q).

proof(rule(if, [TPrf, EPrf], P-if(C, T, E)-Q)) :-
    proof_of(TPrf, [C|P]-T-Q),
    proof_of(EPrf, [not(C)|P]-E-Q).

proof(rule(conseq, [PImp, Prf, QImp], P-S-Q)) :-
    proof_of(PImp, [], P->P2),
    proof_of(QImp, [], Q2->Q),
    proof_of(Prf, P2-S-Q2).

proof(rule(while, [Prf], P-while(C, S)-[not(C)|P])) :-
    proof_of(Prf, [C|P]-S-P).

% ========================
% Useful Facts
% ========================

proof(rule(eq_refl, [], proves(_, X=X))).
proof(rule(eq_sym, [Prf], proves(S, Y=X))) :-
    proof_of(Prf, S, X=Y).
proof(rule(eq_trans, [Prf1, Prf2], proves(S, X=Z))) :-
    proof_of(Prf1, S, X=Y),
    proof_of(Prf2, S, Y=Z).

proof(rule(rewrite, [EqPrf, Prf], proves(S, P))) :-
    proof_of(EqPrf, S, X=E),
    substitute(X, E, P, Q),
    proof_of(Prf, S, Q).

proof(rule(func_eq, [Prf], proves(S, FX=FY))) :-
    FX =.. [F|X],
    FY =.. [F|Y],
    proof_of(Prf, S, X=Y).

proof(rule(add_zero, [], proves(_, 0+N=N))).
proof(rule(add_succ, [], proves(_, s(N)+M=s(N+M)))).
proof(rule(mul_zero, [], proves(_, 0*_=0))).
proof(rule(mul_succ, [], proves(_, s(N)*M = M + N*M))).
proof(rule(nat_eq, [Prf], proves(S, N=M))) :-
    proof_of(Prf, S, s(N)=s(M)).
proof(rule(nat_succ_nonzero, [], proves(_, not(s(_)=0)))).
proof(rule(nat_induct, [ZeroPrf, SuccPrf], proves(S, forall(N, P)))) :-
    substitute(N, 0, P, ZeroP),
    proof_of(ZeroPrf, S, ZeroP),
    substitute(N, s(N), P, SuccP),
    proof_of(SuccPrf, S, forall(N, P->SuccP)).

proof(rule(compute, [], proves(S, P))) :-
    final_step(st(S, P), st(S, true)).
proof(rule(compute_false, [], proves(S, not(P)))) :-
    final_step(st(S, P), st(S, false)).

% ========================
% Utilities
% ========================

proof_of(rule(Rule, Prems, proves(S, P)), S, P) :-
    proof(rule(Rule, Prems, proves(S, P))).

proof_of(rule(Rule, Prems, P-S-Q), P-S-Q) :-
    proof(rule(Rule, Prems, P-S-Q)).

fresh(S, X) :-
    nonvar(X),
    not(free_var(S, X)).
fresh(S, X) :-
    var(X),
    length(_, N),
    term_to_atom(N, X),
    not(free_var(S, X)).

free_var(S, X) :-
    member(P, S),
    free_var(P, X).
free_var(X, X) :- atom(X).
free_var(forall(X, P), Y) :-
    dif(X, Y),
    free_var(P, Y).
free_var(exists(X, P), Y) :-
    dif(X, Y),
    free_var(P, Y).
free_var(P, X) :-
    P =.. [F|Args],
    dif(F, forall),
    dif(F, exists),
    member(Arg, Args),
    free_var(Arg, X).

% substitute(X, E, T1, T2) \iff T1[E/X] = T2 (replacing occurrences of a variable X with E in T1 gives T2).
substitute(_, _, N, N) :- integer(N).
substitute(X, E, X, E).
substitute(X, _E, Y, Y) :- (var(Y) ; atom(Y)), dif(X, Y).
substitute(X, _E, forall(X, P), forall(X, P)).
substitute(X, _E, exists(X, P), exists(X, P)).
substitute(X, E, forall(Y, P), forall(Y, PS)) :-
    dif(X, Y),
    substitute(X, E, P, PS).
substitute(X, E, exists(Y, P), exists(Y, PS)) :-
    dif(X, Y),
    substitute(X, E, P, PS).
substitute(X, E, P, PS) :-
    P =.. [F,Arg|Args],
    dif(F, forall),
    dif(F, exists),
    maplist(substitute(X, E), [Arg|Args], ArgsSub),
    PS =.. [F|ArgsSub].
substitute(_X, _E, [], []).

% ========================
% Inferred Rules
% ========================

extract_body(P, P) :-
    not(functor(P, forall, _)),
    not(functor(P, exists, _)).
extract_body(forall(_, P), Body) :-
    extract_body(P, Body).

all_dif([]).
all_dif([H|T]) :-
    maplist(dif(H), T),
    all_dif(T).

dif_zip([], _, _).
dif_zip([X|Xs], Before, [V|After]) :-
    maplist(dif(X), Before),
    maplist(dif(X), After),
    dif_zip(Xs, [V|Before], After).

inferred_rule(Name, Prf) :-
    Prf = rule(_, _, proves([], P)),
    proof(Prf),
    extract_body(P, Body),
    fresh_body(Body, FreshBody),
    asserta(proof(rule(Name, [], proves(_, FreshBody)))).

fresh_body(Body, FreshBody) :-
    setof(X, free_var(Body, X), Xs),
    length(Xs, N),
    length(FreshVars, N),
    all_dif(FreshVars),
    dif_zip(FreshVars, [], Xs),
    foldl(substitute, Xs, FreshVars, Body, FreshBody).

% Prove n+0=n (we only assume 0+n=n in our axioms).
:- inferred_rule(add_zero_r,
    rule(nat_induct, [
        rule(add_zero, [], proves([], 0+0=0)),
        rule(allI, [
            rule(impI, [
                rule(rewrite, [
                    rule(add_succ, [], proves([n+0=n], s(n)+0=s(n+0))),
                    rule(rewrite, [
                        rule(assm, [], proves([n+0=n], n+0=n)),
                        rule(eq_refl, [], proves(_, s(n)=s(n)))
                    ], proves([n+0=n], s(n+0)=s(n)))
                ], proves([n+0=n], s(n)+0=s(n)))
            ], proves([], (n+0=n)->(s(n)+0=s(n))))
        ], proves([], forall(n, (n+0=n)->(s(n)+0=s(n)))))
    ], proves([], forall(n, n+0=n)))).

% Prove s(n)+m=n+s(m)
:- inferred_rule(add_succ_comm,
    rule(nat_induct, [
        rule(allI, [
            rule(rewrite, [
                rule(add_succ, [], proves([], s(0)+m=s(0+m))),
                rule(rewrite, [
                    rule(add_zero, [], proves([], 0+m=m)),
                    rule(rewrite, [
                        rule(add_zero, [], proves([], 0+s(m)=s(m))),
                        rule(eq_refl, [], proves([], s(m)=s(m)))
                    ], proves([], s(m)=0+s(m)))
                ], proves([], s(0+m)=0+s(m)))
            ], proves([], s(0)+m=0+s(m)))
        ], proves([], forall(m, s(0)+m=0+s(m)))),
        rule(allI, [
            rule(impI, [
                rule(allI, [
                    rule(rewrite, [
                        rule(add_succ, [], proves(_, s(s(n))+k=s(s(n)+k))),
                        rule(rewrite, [
                            rule(add_succ, [], proves(_, s(n)+s(k)=s(n+s(k)))),
                            rule(rewrite, [
                                rule(allE, [rule(assm, [], proves(_, forall(m, s(n)+m=n+s(m))))], proves(_, s(n)+k=n+s(k))),
                                rule(eq_refl, [], proves(_, s(n+s(k))=s(n+s(k))))
                            ], proves(_, s(s(n)+k) = s(n+s(k))))
                        ], proves(_, s(s(n)+k)=s(n)+s(k)))
                    ], proves([forall(m, s(n)+m=n+s(m))], s(s(n))+k=s(n)+s(k)))
                ], proves([forall(m, s(n)+m=n+s(m))], forall(m, s(s(n))+m=s(n)+s(m))))
            ], proves([], forall(m, s(n)+m=n+s(m)) -> forall(m, s(s(n))+m=s(n)+s(m))))
        ], proves([], forall(n, forall(m, s(n)+m=n+s(m)) -> forall(m, s(s(n))+m=s(n)+s(m)))))
    ], proves([], forall(n, forall(m, s(n)+m=n+s(m)))))).

% Prove natural number addition is commutative
:- inferred_rule(add_comm,
    rule(nat_induct, [
        rule(allI, [
            rule(rewrite, [
                rule(add_zero, [], proves([], 0+m=m)),
                rule(eq_sym, [
                    rule(add_zero_r, [], proves([], m+0=m))
                ], proves([], m=m+0))
            ], proves([], 0+m=m+0))
        ], proves([], forall(m, 0+m=m+0))),
        rule(allI, [
            rule(impI, [
                rule(allI, [
                    rule(rewrite, [
                        rule(add_succ, [], proves(_, s(n)+k=s(n+k))),
                        rule(rewrite, [
                            rule(rewrite, [
                                rule(eq_sym, [
                                    rule(add_succ, [], proves(_, s(k)+n=s(k+n)))
                                ], proves(_, s(k+n)=s(k)+n)),
                                rule(eq_sym, [
                                    rule(add_succ_comm, [], proves(_, s(k)+n=k+s(n)))
                                ], proves(_, k+s(n)=s(k)+n))
                            ], proves([forall(m, n+m=m+n)], k+s(n)=s(k+n))),
                            rule(rewrite, [
                                rule(allE, [
                                    rule(assm, [], proves(_, forall(m, n+m=m+n)))
                                ], proves(_, n+k=k+n)),
                                rule(eq_refl, [], proves(_, s(k+n)=s(k+n)))
                            ], proves(_, s(n+k)=s(k+n)))
                        ], proves([forall(m, n+m=m+n)], s(n+k)=k+s(n)))
                    ], proves(_, s(n)+k=k+s(n)))
                ], proves([forall(m, n+m=m+n)], forall(m, s(n)+m=m+s(n))))
            ], proves([], forall(m, n+m=m+n) -> forall(m, s(n)+m=m+s(n))))
        ], proves([], forall(n, forall(m, n+m=m+n) -> forall(m, s(n)+m=m+s(n)))))
    ], proves([], forall(n, forall(m, n+m=m+n))))).

% ========================
% Program Execution
% ========================

% e + e, e - e, e * e, integer, x
% x := e
% skip
% if e { e } else { e }
% while e { e }
% s ; s

value(true).
value(false).
value(N) :- integer(N).

% Expressions
step(st(Memory, X), st(Memory, V)) :- atom(X), member(X=V, Memory).
step(st(Memory, X), st(Memory, V)) :- atom(X), member(V=X, Memory).

step(st(Memory, E1+E2), st(NewMemory, NewE1+E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1+E2), st(NewMemory, E1+NewE2)) :-
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1+V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 + V2.

step(st(Memory, E1-E2), st(NewMemory, NewE1-E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1-E2), st(NewMemory, E1-NewE2)) :-
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1-V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 - V2.

step(st(Memory, E1*E2), st(NewMemory, NewE1*E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1*E2), st(NewMemory, E1*NewE2)) :-
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1*V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 * V2.

step(st(Memory, E1=E2), st(NewMemory, NewE1=E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1=E2), st(NewMemory, E1=NewE2)) :-
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V=V), st(Memory, true)) :- value(V).
step(st(Memory, V=W), st(Memory, false)) :- value(V), value(W), dif(V, W).

:- op(700, yfx, <=).

step(st(Memory, E1<=E2), st(NewMemory, NewE1<=E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1<=E2), st(NewMemory, E1<=NewE2)) :-
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V<=W), st(Memory, true)) :- value(V), value(W), V #=< W.
step(st(Memory, V<=W), st(Memory, false)) :- value(V), value(W), V #> W.

% Statements
step(st(Memory, skip ; S2), st(Memory, S2)).

step(st(Memory, S1 ; S2), st(NewMemory, NewS1 ; S2)) :-
    step(st(Memory, S1), st(NewMemory, NewS1)).

step(st(Memory, X := E), st(NewMemory, X := NewE)) :-
    step(st(Memory, E), st(NewMemory, NewE)).
step(st(Memory, X := V), st(NewMemory, skip)) :-
    value(V),
    select(X=_, Memory, Temp),
    select(X=V, NewMemory, Temp).

step(st(Memory, if(C, T, E)), st(NewMemory, if(NewC, T, E))) :-
    step(st(Memory, C), st(NewMemory, NewC)).
step(st(Memory, if(true, T, _E)), st(Memory, T)).
step(st(Memory, if(false, _T, E)), st(Memory, E)).

step(st(Memory, while(C, Body)), st(Memory, if(C, Body ; while(C, Body), skip))).

many_step(State, State).
many_step(State1, State2) :-
    step(State1, Temp),
    many_step(Temp, State2).

final_step(Init, Final) :- many_step(Init, Final), not(step(Final, _)).

init_to(V, X, X=V).
run(P, ResultMemory) :-
    setof(X, free_var(P, X), Xs),
    maplist(init_to(0), Xs, InitMemory),
    final_step(st(InitMemory, P), st(ResultMemory, skip)).

