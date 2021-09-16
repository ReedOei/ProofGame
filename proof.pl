:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).

:- use_module(library(achelois)).

% Language:
% e + e, e - e, e * e, integer, x
% x := e
% skip
% if e { e } else { e }
% while e { e }
% s ; s

:- dynamic proof_tree/2.
:- discontiguous proof/1.
:- dynamic inference_rule/3.
:- discontiguous inference_rule/3.

form_rule(Conclusion, rule(_, _, Conclusion)).
proof(rule(Name, Prems, Conclusion)) :-
    inference_rule(Name, ToShow, Conclusion),
    maplist(form_rule, ToShow, Prems),
    forall(member(Prem, Prems), proof(Prem)).

% ========================
% First order logic
% ========================

proof(rule(assm, [], proves(S, P))) :- member(P, S).

inference_rule(trueI, [], proves(_, true)).
inference_rule(falseE, [proves(S, false)], proves(S, _)).

inference_rule(notI, [proves([A|S], false)], proves(S, not(A))).
inference_rule(notE, [
    proves(S, A),
    proves(S, not(A))
], proves(S, _)).

inference_rule(orIL, [proves(S, A)], proves(S, A\/_)).
inference_rule(orIR, [proves(S, B)], proves(S, _\/B)).
inference_rule(orE, [
    proves(S, A\/B),
    proves([A|S], C),
    proves([B|S], C)
], proves(S, C)).

proves_conc(S, Conc, rule(_, _, proves(S, Conc))).
proof(rule(andI, Prems, proves(S, Conjs))) :-
    maplist(proves_conc(S), Conjs, Prems),
    forall(member(Prem, Prems), proof(Prem)).
proof(rule(andE, [rule(_, _, proves(S, Conjs))], proves(S, Conc))) :-
    member(Conc, Conjs).

inference_rule(impI, [proves([A|S], B)], proves(S, A->B)).
inference_rule(impE, [
    proves(S, A->B),
    proves(S, A)
], proves(S, B)).

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

proof(rule(assign, [], P-(X:=E)-Q)) :-
    substitute(X, E, Q, P).

inference_rule(skip, [], P-skip-P).

inference_rule(seq, [
    P-S1-R,
    R-S2-Q
], P-(S1;S2)-Q).

inference_rule(if, [
    [C|P]-T-Q,
    [not(C)|P]-E-Q
], P-if(C, T, E)-Q).

inference_rule(weaken, [
    proves(Q2, Q),
    P-S-Q2
], P-S-Q).

inference_rule(strengthen, [
    proves(P, P2),
    P2-S-Q
], P-S-Q).

inference_rule(while, [
    [C|P]-S-P
], P-while(C,S)-[not(C)|P]).

% ========================
% Useful Facts
% ========================
inference_rule(eq_refl, [], proves(_, X=X)).

inference_rule(eq_sym, [proves(S, X=Y)], proves(S, Y=X)).

inference_rule(eq_trans, [
    proves(S, X=Y),
    proves(S, Y=Z)
], proves(S, X=Z)).

inference_rule(leq_refl, [], proves(_, X<=X)).

inference_rule(leq_antisym, [proves(S, X<=Y), proves(S, Y<=X)], proves(S, X=Y)).

inference_rule(leq_trans, [
    proves(S, X<=Y),
    proves(S, Y<=Z)
], proves(S, X<=Z)).

inference_rule(leq_total, [], proves(_, (X<=Y)\/(Y<=X))).

inference_rule(add_zero, [], proves(_, 0+N=N)).
inference_rule(add_succ, [], proves(_, s(N)+M=s(N+M))).
inference_rule(mul_zero, [], proves(_, 0*_=0)).
inference_rule(mul_succ, [], proves(_, s(N)*M = M + N*M)).
inference_rule(nat_eq, [proves(S, s(N)=s(M))], proves(S, N=M)).
inference_rule(nat_succ_nonzero, [], proves(_, not(s(_)=0))).

proof(rule(nat_induct, [ZeroPrf, SuccPrf], proves(S, forall(N, P)))) :-
    substitute(N, 0, P, ZeroP),
    proof_of(ZeroPrf, S, ZeroP),
    substitute(N, s(N), P, SuccP),
    proof_of(SuccPrf, S, forall(N, P->SuccP)).

proof(rule(rewrite, [EqPrf, Prf], proves(S, P))) :-
    proof_of(EqPrf, S, X=E),
    substitute(X, E, P, Q),
    proof_of(Prf, S, Q).

proof(rule(func_eq, [Prf], proves(S, FX=FY))) :-
    FX =.. [F|X],
    FY =.. [F|Y],
    proof_of(Prf, S, X=Y).

% proof(rule(compute, [], proves(S, P))) :-
%     final_step(st(S, P), st(S, true)).
% proof(rule(compute_false, [], proves(S, not(P)))) :-
%     final_step(st(S, P), st(S, false)).

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
    Prf = rule(_, _, proves(S, P)),
    proof(Prf),
    extract_body(P, Body),
    fresh_body(Body, FreshBody),
    asserta(inference_rule(Name, [], proves(S, FreshBody))),
    asserta(proof_tree(Name, Prf)).

inferred_rule(Name, Prf) :-
    Prf = rule(_, _, P-S-Q),
    proof(Prf),
    fresh_body(P-S-Q, FreshBody),
    asserta(inference_rule(Name, [], FreshBody)),
    asserta(proof_tree(Name, Prf)).

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
                        rule(eq_refl, [], proves([n+0=n], s(n)=s(n)))
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
                        rule(add_succ, [], proves([forall(m, s(n)+m=n+s(m))], s(s(n))+k=s(s(n)+k))),
                        rule(rewrite, [
                            rule(add_succ, [], proves([forall(m, s(n)+m=n+s(m))], s(n)+s(k)=s(n+s(k)))),
                            rule(rewrite, [
                                rule(allE, [rule(assm, [], proves([forall(m, s(n)+m=n+s(m))], forall(m, s(n)+m=n+s(m))))], proves([forall(m, s(n)+m=n+s(m))], s(n)+k=n+s(k))),
                                rule(eq_refl, [], proves([forall(m, s(n)+m=n+s(m))], s(n+s(k))=s(n+s(k))))
                            ], proves([forall(m, s(n)+m=n+s(m))], s(s(n)+k) = s(n+s(k))))
                        ], proves([forall(m, s(n)+m=n+s(m))], s(s(n)+k)=s(n)+s(k)))
                    ], proves([forall(m, s(n)+m=n+s(m))], s(s(n))+k=s(n)+s(k)))
                ], proves([forall(m, s(n)+m=n+s(m))], forall(m, s(s(n))+m=s(n)+s(m))))
            ], proves([], forall(m, s(n)+m=n+s(m)) -> forall(m, s(s(n))+m=s(n)+s(m))))
        ], proves([], forall(n, forall(m, s(n)+m=n+s(m)) -> forall(m, s(s(n))+m=s(n)+s(m)))))
    ], proves([], forall(n, forall(m, s(n)+m=n+s(m)))))).

% Prove n+m=n+m
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
                        rule(add_succ, [], proves([forall(m, n+m=m+n)], s(n)+k=s(n+k))),
                        rule(rewrite, [
                            rule(rewrite, [
                                rule(eq_sym, [
                                    rule(add_succ, [], proves([forall(m, n+m=m+n)], s(k)+n=s(k+n)))
                                ], proves([forall(m, n+m=m+n)], s(k+n)=s(k)+n)),
                                rule(eq_sym, [
                                    rule(add_succ_comm, [], proves([forall(m, n+m=m+n)], s(k)+n=k+s(n)))
                                ], proves([forall(m, n+m=m+n)], k+s(n)=s(k)+n))
                            ], proves([forall(m, n+m=m+n)], k+s(n)=s(k+n))),
                            rule(rewrite, [
                                rule(allE, [
                                    rule(assm, [], proves([forall(m, n+m=m+n)], forall(m, n+m=m+n)))
                                ], proves([forall(m, n+m=m+n)], n+k=k+n)),
                                rule(eq_refl, [], proves([forall(m, n+m=m+n)], s(k+n)=s(k+n)))
                            ], proves([forall(m, n+m=m+n)], s(n+k)=s(k+n)))
                        ], proves([forall(m, n+m=m+n)], s(n+k)=k+s(n)))
                    ], proves([forall(m, n+m=m+n)], s(n)+k=k+s(n)))
                ], proves([forall(m, n+m=m+n)], forall(m, s(n)+m=m+s(n))))
            ], proves([], forall(m, n+m=m+n) -> forall(m, s(n)+m=m+s(n))))
        ], proves([], forall(n, forall(m, n+m=m+n) -> forall(m, s(n)+m=m+s(n)))))
    ], proves([], forall(n, forall(m, n+m=m+n))))).

:- inferred_rule(example_add,
    rule(strengthen, [
        rule(andI, [
            rule(eq_refl, [], proves([], a+b=a+b))
        ], proves([], [a+b=a+b])),
        rule(assign, [], [a+b=a+b]-(x:=a+b)-[x=a+b])
    ], []-(x:=a+b)-[x=a+b])).

:- inferred_rule(example_max,
    rule(if, [
        rule(strengthen, [
            rule(andI, [
                rule(assm, [], proves([x <= y], x <= y)),
                rule(leq_refl, [], proves([x <= y], y <= y))
            ], proves([x <= y], [x <= y, y <= y])),
            rule(assign, [], [x <= y, y <= y]-(m := y)-[x <= m, y <= m])
        ], [x <= y]-(m := y)-[x <= m, y <= m]),

        rule(strengthen, [
            rule(andI, [
                rule(leq_refl, [], proves([not(x <= y)], x <= x)),
                rule(orE, [
                    rule(leq_total, [], proves([not(x <= y)], (x <= y)\/(y <= x))),
                    rule(notE, [
                        rule(assm, [], proves([x <= y, not(x <= y)], x <= y)),
                        rule(assm, [], proves([x <= y, not(x <= y)], not(x <= y)))
                    ], proves([x <= y, not(x <= y)], y <= x)),
                    rule(assm, [], proves([y <= x, not(x <= y)], y <= x))
                ], proves([not(x <= y)], y <= x))
            ], proves([not(x <= y)], [x <= x, y <= x])),
            rule(assign, [], [x <= x, y <= x]-(m := x)-[x <= m, y <= m])
        ], [not(x <= y)]-(m := x)-[x <= m, y <= m])
    ], []-if(x <= y, m := y, m := x)-[x <= m, y <= m])).

% ========================
% Program Execution
% ========================

value(true).
value(false).
value(N) :- integer(N).

% Expressions
step(st(Memory, X), st(Memory, V)) :- atom(X), member(X=V, Memory).
step(st(Memory, X), st(Memory, V)) :- atom(X), member(V=X, Memory).

step(st(Memory, E1+E2), st(NewMemory, NewE1+E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1+E2), st(NewMemory, E1+NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1+V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 + V2.

step(st(Memory, E1-E2), st(NewMemory, NewE1-E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1-E2), st(NewMemory, E1-NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1-V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 - V2.

step(st(Memory, E1*E2), st(NewMemory, NewE1*E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1*E2), st(NewMemory, E1*NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V1*V2), st(Memory, S)) :-
    integer(V1),
    integer(V2),
    S #= V1 * V2.

step(st(Memory, E1=E2), st(NewMemory, NewE1=E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1=E2), st(NewMemory, E1=NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V=V), st(Memory, true)) :- value(V).
step(st(Memory, V=W), st(Memory, false)) :- value(V), value(W), dif(V, W).

:- op(700, yfx, <=).
:- op(700, yfx, >=).

step(st(Memory, E1<=E2), st(NewMemory, NewE1<=E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1<=E2), st(NewMemory, E1<=NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V<=W), st(Memory, true)) :- value(V), value(W), V #=< W.
step(st(Memory, V<=W), st(Memory, false)) :- value(V), value(W), V #> W.

step(st(Memory, E1<E2), st(NewMemory, NewE1<E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1<E2), st(NewMemory, E1<NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V<W), st(Memory, true)) :- value(V), value(W), V #< W.
step(st(Memory, V<W), st(Memory, false)) :- value(V), value(W), V #>= W.

step(st(Memory, E1>E2), st(NewMemory, NewE1>E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1>E2), st(NewMemory, E1>NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V>W), st(Memory, true)) :- value(V), value(W), V #> W.
step(st(Memory, V>W), st(Memory, false)) :- value(V), value(W), V #=< W.

step(st(Memory, E1>=E2), st(NewMemory, NewE1>=E2)) :-
    step(st(Memory, E1), st(NewMemory, NewE1)).
step(st(Memory, E1>=E2), st(NewMemory, E1>=NewE2)) :-
    value(E1),
    step(st(Memory, E2), st(NewMemory, NewE2)).
step(st(Memory, V>=W), st(Memory, true)) :- value(V), value(W), V #>= W.
step(st(Memory, V>=W), st(Memory, false)) :- value(V), value(W), V #< W.

% Statements
step(st(Memory, skip ; S2), st(Memory, S2)).

step(st(Memory, S1 ; S2), st(NewMemory, NewS1 ; S2)) :-
    step(st(Memory, S1), st(NewMemory, NewS1)).

step(st(Memory, X := E), st(NewMemory, X := NewE)) :-
    step(st(Memory, E), st(NewMemory, NewE)).
step(st(Memory, X := V), st([X=V|Temp], skip)) :-
    value(V),
    select(X=_, Memory, Temp).

step(st(Memory, if(C, T, E)), st(NewMemory, if(NewC, T, E))) :-
    step(st(Memory, C), st(NewMemory, NewC)).
step(st(Memory, if(true, T, _E)), st(Memory, T)).
step(st(Memory, if(false, _T, E)), st(Memory, E)).

step(st(Memory, while(C, Body)), st(Memory, if(C, Body ; while(C, Body), skip))).

many_step(0, State, State).
many_step(N, State1, State2) :-
    N #> 0,
    N1 #= N - 1,
    step(State1, Temp),
    many_step(N1, Temp, State2).

final_step(N, Init, Final) :-
    many_step(N, Init, Final),
    not(step(Final, _)).

init_to(V, X, X=V).
run(N, P, ResultMemory) :-
    setof(X, free_var(P, X), Xs),
    maplist(init_to(0), Xs, InitMemory),
    final_step(N, st(InitMemory, P), st(ResultMemory, skip)).

% ========================
% Parsing
% ========================

phrase_atom(F, A) :-
    nonvar(A),
    atom_codes(A, C),
    phrase(F, C).
phrase_atom(F, A) :-
    var(A),
    phrase(F, C),
    atom_codes(A, C).

letter(A) --> [A], { A in 65..90 \/ 97..122 }.

letters([A|Rest]) --> letter(A), letters_cont(Rest).
letters_cont([]) --> [].
letters_cont([A|Rest]) --> letter(A), letters_cont(Rest).

arguments([]) --> blanks, ")".
arguments([F|Rest]) --> top_formula(F), blanks, ("," ; ";"), blanks, arguments(Rest).
arguments([F]) --> top_formula(F), blanks, ")".

constant_formula(X) --> number(X).
constant_formula(S) --> [34], string_without([34], Codes), [34], { atom_codes(S, Codes) }. % char_code('"', 34).

atomic_formula(F) --> constant_formula(F).
atomic_formula(X) --> letters(XCodes), { atom_codes(X, XCodes) }.
atomic_formula(func(F, Args)) -->
    letters(FCodes), { atom_codes(F, FCodes) },
    blanks, "(", blanks,
    arguments(Args).

atomic_formula(F) --> "(", blanks, top_formula(F), blanks, ")".

pow_formula(F) -->
    atomic_formula(L),
    (
        blanks, "^", blanks, pow_formula(R) -> { F = pow(L, R) };
        { F = L }
    ).

neg_formula(F) --> pow_formula(F).
neg_formula(neg(F)) --> "-", blanks, pow_formula(F).

mul_sym(L, R, L*R) --> "*".
mul_formula(F) -->
    neg_formula(L),
    (
        blanks, mul_sym(L, R, F), blanks, mul_formula(R);
        { F = L }
    ).

add_sym(L, R, L+R) --> "+".
add_sym(L, R, L-R) --> "-".
add_formula(F) -->
    mul_formula(L),
    (
        blanks, add_sym(L, R, F), blanks, add_formula(R);
        { F = L }
    ).

bool_sym(L, R, L<R) --> "<".
bool_sym(L, R, L<=R) --> "<=".
bool_sym(L, R, L>R) --> ">".
bool_sym(L, R, L>=R) --> ">=".
bool_sym(L, R, L=R) --> "=".
bool_sym(L, R, not(L=R)) --> "!=".
bool_formula(F) -->
    add_formula(L),
    (
        blanks, bool_sym(L, R, F), blanks, add_formula(R);
        { F = L }
    ).

top_formula(F) --> bool_formula(F).

statement(X:=E) --> letters(XCodes), { atom_codes(X, XCodes) }, blanks, ":=", blanks, top_formula(E).

statement(if(C, T, E)) -->
    "if", blanks, top_formula(C), blanks, "{", blanks,
        program(T), blanks,
    "}", blanks, "else", blanks, "{", blanks,
        program(E), blanks,
    "}".

statement(while(C, Body)) -->
    "while", blanks, top_formula(C), blanks, "{", blanks,
        program(Body), blanks,
    "}".

program(S) --> statement(S).
program(S1;S2) --> statement(S1), blanks, ";", blanks, program(S2).

% ========================
% Latex
% ========================

latex_prems([]) --> "".
latex_prems([P|Ps]) --> latex(P), "\\\\", latex_prems(Ps).

latex_assms([]) --> "".
latex_assms([P]) --> latex(P).
latex_assms([P1,P2|Ps]) --> latex(P1), ",", latex_assms([P2|Ps]).

latex(s(N)) --> "s(", latex(N), ")".

latex(X) --> { when(nonvar(X), atom(X)) }, atom(X).
latex(N) --> { when(nonvar(N), integer(N)) }, integer(N).
latex(A<=B) --> latex(A), " \\leq ", latex(B).
latex(A+B) --> latex(A), "+", latex(B).
latex(A-B) --> { not(is_list(A)), not(is_list(B)) }, latex(A), "-", latex(B).
latex(A*B) --> latex(A), "*", latex(B).
latex(A=B) --> latex(A), "=", latex(B).
latex(X:=E) --> latex(X), " := ", latex(E).
latex(skip) --> "skip".
latex(if(C, T, E)) -->
    "\\textbf{if}~", latex(C),
    "~\\{~", latex(T),
    "~\\}~\\textbf{else}~\\{~", latex(E),
    "~\\}".
latex(while(C, Body)) -->
    "\\textbf{while}~", latex(C),
    "\\{~", latex(Body),
    "\\}".

latex(true) --> "true".
latex(false) --> "false".
latex(not(P)) --> "\\lnot (", latex(P), ")".
latex(P->Q) --> latex(P), " ", "\\Rightarrow", " ", latex(Q).
latex(P/\Q) --> latex(P), " ", "\\land", " ", latex(Q).
latex(P\/Q) --> latex(P), " ", "\\lor", " ", latex(Q).

latex(forall(X, P)) --> "\\forall", " ", latex(X), ".", latex(P).
latex(exists(X, P)) --> "\\exists", " ", latex(X), ".", latex(P).

latex(Ps) --> "\\{", latex_assms(Ps), "\\}".

latex(proves(S, P)) --> latex(S), " ", "\\vdash", " ", latex(P).

latex(P-S-Q) -->
    latex(P), "~", latex(S), "~", latex(Q).

latex(rule(Name, Prems, Con)) -->
    "\\inferrule*[right=", { when(nonvar(Name), atom(Name)), rule_name(Name, OutName) }, atom(OutName), "]{",
    latex_prems(Prems),
    " }{", latex(Con), "}".

rule_name(Name, OutputName) :-
    atomic_list_concat(Parts, '_', Name),
    atomic_list_concat(Parts, '-', OutputName).

write_latex(P) :-
    phrase_atom(latex(P), PStr),
    read_file('header.tex', Header),
    read_file('footer.tex', Footer),
    atomic_list_concat([Header, PStr, Footer], '\n', Out),
    write_file('temp.tex', Out),

    process(path(pdflatex), ['temp.tex']),
    process(path('xdg-open'), ['temp.pdf']).

