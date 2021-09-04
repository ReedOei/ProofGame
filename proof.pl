% Language:
% e + e, e - e, e * e, integer, x
% x := e
% skip
% if e { e } else { e }
% while e { e }
% s ; s

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
    fresh([forall(X, P)|S], Y),
    substitute(X, Y, P, Q),
    proof_of(Prf, S, Q).
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
    fresh([exists(X, P)|S], Y),
    substitute(X, Y, P, Q),
    proof_of(UsePrf, [Q|S], C).

% ========================
% Hoare Logic
% ========================

proof(rule(skip, [], P-skip-P)).

proof(rule(assign, [], P-(X:=E)-Q)) :-
    substitute(X, E, Q, P).

proof(rule(seq, [S1Prf, S2Prf], P-(S1;S2)-Q)) :-
    S1Prf = rule(_, _, P-S1-R),
    proof(S1Prf),
    S2Prf = rule(_, _, R-S2-Q),
    proof(S2Prf).

proof(rule(if, [TPrf, EPrf], P-if(C, T, E)-Q)) :-
    TPrf = rule(_, _, [C|P]-T-Q),
    proof(TPrf),
    EPrf = rule(_, _, [not(C)|P]-E-Q),
    proof(EPrf).

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

proof(rule(func_eq, [Prf], proves(S, FX=FY))) :-
    FX =.. [F|X],
    FY =.. [F|Y],
    proof_of(Prf, S, X=Y).

proof(rule(add_comm, [], proves(_, N+M=M+N))).
proof(rule(nat_eq, [Prf], proves(S, N=M))) :-
    proof_of(Prf, S, s(N)=s(M)).
proof(rule(nat_succ_nonzero, [], proves(_, not(s(_)=0)))).

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
substitute(X, _E, Y, Y) :- atom(Y), dif(X, Y).
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
% Example Proofs
% ========================
% Use add_comm schema to get a universal quantifier version
proof_example(
    rule(allI,
        [rule(allI,
            [rule(add_comm, [], proves([], X+Y=Y+X))],
            proves([], forall(m, X+m=m+X)))],
        proves([], forall(n, forall(m, n+m=m+n))))).

