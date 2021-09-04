% Language:
% e + e, e - e, e * e, integer, x
% x := e
% skip
% if e { e } else { e }
% while e { e }
% s ; s

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
    PImp = rule(_, _, P->P2),
    proof(PImp),
    QImp = rule(_, _, Q2->Q),
    proof(QImp),
    Prf = rule(_, _, P2-S-Q2),
    proof(Prf).
proof(rule(while, [Prf], P-while(C, S)-[not(C)|P])) :-
    Prf = rule(_, _, [C|P]-S-P),
    proof(Prf).

rule(
