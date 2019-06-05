%%%%%%%%%%%%
% sat(F,I,M)
% si F es satisfactible, M sera el model de F afegit a la interpretació I (a la primera crida I sera buida).
% Assumim invariant que no hi ha literals repetits a les clausules ni la clausula buida inicialment.

sat([],I,I):-     write('SAT!!'),nl,!.
sat(CNF,I,M):-
% Ha de triar un literal d’una clausula unitaria, si no n’hi ha cap, llavors un literal pendent qualsevol.
decideix(CNF,Lit),

% Simplifica la CNF amb el Lit triat (compte pq pot fallar, es a dir si troba la clausula buida fallara i fara backtraking).
simplif(Lit,CNF,CNFS),

% crida recursiva amb la CNF i la interpretacio actualitzada
append(I, [Lit], R),
sat(CNFS,R,M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
decideix([[X|_]|[]], X):- !.
decideix([X|_], Lit):- X = [_|_], decideixN(X, Lit), !.
decideix([_|Y], Lit):- decideix(Y, Lit).

decideixN([X], X).



%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
simplif(_, [], []).
simplif(X, [Y|XS], LS):- Y \= [_|_], M is -X, M =:= Y, simplif(X, XS, LS), !.
simplif(X, [CNF|CNFS], [F|FS]) :- CNF = [_|_], simplif(X, CNF, F), simplif(X, CNFS, FS), !.
simplif(X, [Head|Tail], [Head|TailResult]) :- Head \= [_|_], simplif(X, Tail, TailResult), !.