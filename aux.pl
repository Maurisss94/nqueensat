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
append([Lit], I, R),
sat(CNFS,R,M).

%%%%%%%%%%%%%%%%%%
% decideix(F, Lit)
% Donat una CNF,
% -> el segon parametre sera un literal de CNF
%  - si hi ha una clausula unitaria sera aquest literal, sino
%  - un qualsevol o el seu negat.
% Mauro:
decideix(L, X):- member([X], L), !.
decideix([[L|_]|_], L).
decideix([[L|_]|_], P):- P is -L.

%%%%%%%%%%%%%%%%%%%%%
% simplif(Lit, F, FS)
% Donat un literal Lit i una CNF,
% -> el tercer parametre sera la CNF que ens han donat simplificada:
%  - sense les clausules que tenen lit
%  - treient -Lit de les clausules on hi es, si apareix la clausula buida fallara.
% Mauro:
simplif(_, [], []).
simplif(X, [L|LS], CNFS) :- member(X, L),!, simplif(X, LS, CNFS),!.
simplif(X, [Y|XS], LS):- M is -X,
                                            append(A, [M|MS], Y),!,
                                            append(A, MS, RES), RES \=[],
                                            simplif(X, XS, CUACNFS),
                                            append([RES], CUACNFS, LS),!.
simplif(X, [CNF|CNFS], [F|FS]) :-  CNF = [_|_], simplif(X, CNF, F), simplif(X, CNFS, FS), !.
simplif(X, [Head|Tail], [Head|TailResult]) :- Head \= [_|_], simplif(X, Tail, TailResult), !.


% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

% Passa una llista de diagonals a llistes de llistes de variables
llistesDiagonalsAVars([], _, []).
llistesDiagonalsAVars([Lparells|LS],N,Lvars):- coordenadesAVars(Lparells, N, R), llistesDiagonalsAVars(LS, N, F), append([R], F, Lvars).

% AUX
% trosseja(L,N,LL)
% Donada una llista (L) i el numero de trossos que en volem (N)
% -> LL sera la llista de N llistes de L amb la mateixa mida
% (S'assumeix que la llargada de L i N ho fan possible)
% Mauro: Agafa els N, elements de L, i crida recursiva, amb els elements que seran tambe del tercer parametre.
trosseja([], _, []).
trosseja(L, N, [LL|LS]):- length(LL, N), append(LL, R, L), trosseja(R, N, LS).

% AUX
% llista(I,F,L)
% Donat un inici i un fi
% -> el tercer parametre sera una llista de numeros d'inici a fi
% Mauro:
llista(F, F, [F]):- !.
llista(L, F, [L|LS]):- L =< F, N is L+1, llista(N, F, LS).

% AUX
% fixa(PI,N,F)
% donada una llista de tuples de posicions PI i una mida de tauler N
% -> F es la CNF fixant les corresponents variables de posicions a certa
fixa(PS, N, F):- coordenadesAVars(PS, N, R), trosseja(R, 1, F), !.

% AUX
% prohibeix(PP,N,P)
% donada una llista de tuples de posicions prohibides PP i una mida  tauler N
% -> P es la CNF posant les corresponents variables de posicions a fals
prohibeix(PP, N, F):- coordenadesAVars(PP, N, R), negat(R, RN), trosseja(RN, 1, F), !.


% AQUEST PREDICAT ESTA PARCIALMENT FET. CAL QUE CALCULEU LES "ALTRES"
% DIAGONALS
%%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesDiagonals(+N,C)
% donada la mida del tauler,
% -> D sera la CNF que codifiqui que no s'amenecen les reines de les mateixes diagonals
noAmenacesDiagonals(N,D):- diagonals(N,L), llistesDiagonalsAVars(L,N,VARS),noAmenacesDiagonals2(VARS,D).

noAmenacesDiagonals2([],[]).
noAmenacesDiagonals2([L|LS],X):- comamoltUn(L,D),noAmenacesDiagonals2(LS,R),append(D,R,X).

% Genera les llistes de diagonals d'una matriu NxN. Cada diagonal es una llista de coordenades.
diagonals(N,L):- diagonalsIn(1,N,L1), diagonals2In(1,N,L2), append(L1,L2,L).


% diagonalsIn(D,N,L)
% Generem les diagonals baix-esquerra a dalt-dreta, D es el numero de
% diagonals, N la mida del tauler i L seran les diagonals generades
% Exemple:
% ?- diagonalsIn(1,3,L).
% L = [[(1,1)],[(1,2),(2,1)],[(1,3),(2,2),(3,1)],[(2,3),(3,2)],[(3,3)]]
% Evidentment les diagonals amb una sola coordenada les ignorarem...

diagonalsIn(D,N,[]):-D is 2*N,!.
diagonalsIn(D,N,[L1|L]):- D=<N,fesDiagonal(1,D,L1), D1 is D+1, diagonalsIn(D1,N,L).
diagonalsIn(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonalsIn(D1,N,L).

fesDiagonal(F,1,[(F,1)]):- !.
fesDiagonal(F,C,[(F,C)|R]):- F1 is F+1, C1 is C-1, fesDiagonal(F1,C1,R).

% quan la fila es N parem
fesDiagonalReves(N,C,N,[(N,C)]):-!.
fesDiagonalReves(F,C,N,[(F,C)|R]):-F1 is F+1, C1 is C-1, fesDiagonalReves(F1,C1,N,R).

% diagonals2In(D,N,L)
% Generem les diagonals baix-dreta a dalt-esquerra
% Exemple
% ?- diagonals2In(1,3,L).
% L = [[(3,1)],[(3,2),(2,1)],[(3,3),(2,2),(1,1)],[(2,3),(1,2)],[(1,3)]]
diagonals2In(D,N,[]):-D is 2*N,!.
diagonals2In(D,N,[L1|L]):- D<N,fesDiagonal2(N,D,L1), D1 is D+1, diagonals2In(D1,N,L).
diagonals2In(D,N,LS):- D>=N, F is D-N+1,fesDiagonalReves2(F,N,L1), D1 is D+1, diagonals2In(D1,N,L), append(L, [L1], LS).

fesDiagonal2(F,1,[(F,1)]):- !.
fesDiagonal2(F,C,[(F,C)|R]):- F1 is F-1, C1 is C-1, fesDiagonal2(F1,C1,R).

fesDiagonalReves2(1,C,[(1,C)]):-!.
fesDiagonalReves2(F,C,[(F,C)|R]):-F1 is F-1, C1 is C-1, fesDiagonalReves2(F1,C1,R).


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
comaminimUn(L, L).
% comaminimUn([L|LS], CNF):- L > 0, append([L], LS, CNF), !.
% comaminimUn([L|LS], CNF):- comaminimUn(LS,R), append([L], R, CNF).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
comamoltUn([], []).
comamoltUn(L, CNF):- negat(L, NL), combina(NL, CNF).

% negat(L, N).
% Donat una llista de variables booleans,
% -> el segon parametre sera una llista amb les variables negades.
% Ull amb negar les que ja estan NEGADES!!!!
negat([], []).
negat([L|LS], N):- L < 0, negat(LS, R), append([L], R, N), !.
negat([L|LS], N):- L > 0, LN is -L, negat(LS, R), append([LN], R, N).

% combina(L, C).
% Donat una llista de variables booleanes.
% -> el segon parametre es una llista de parelles, fent totes les combinacions  [1,2,3] -> [1,2], [1,3], [2,3]
combina(L, C) :- findall(X0, combinaN(2, L, X0), C).

% combinaN(N, L, R)
% Donat un numero > 0, N, i una llista de variables booleanes, L
% El tercer parametre es una llista de N, amb les combinacions de L
combinaN(0,_,[]).
combinaN(N,L,[X|XS]) :- llistaN(X,L,R), N1 is N-1, combinaN(N1,R,XS).

% Donat un N (numero), i una llista
% El tercer parametre retorna els elements sobrants de la llista a partir del valor de N
llistaN(N,[N|L],R):- append(L, [], R).
llistaN(N,[_|L],R) :- llistaN(N,L,R).


%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes, [1,2,3,-4]
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
exactamentUn(L, CNF):- comaminimUn(L, R), comamoltUn(L, S), append([R], S, CNF).

%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesFiles(+V,F)
% donada la matriu de variables,
% -> F sera la CNF que codifiqui que no s'amenecen les reines de les mateixes files
% V es una matriu = [[1,2,3], [4,5,6], [7,8,9]], de 3 x 3 en aquest cas.
noAmenacesFiles([], []).
noAmenacesFiles([V|VS], F):- exactamentUn(V, FS), noAmenacesFiles(VS, R), append(FS, R, F).


%%%%%%%%%%%%%%%%%%%%%%%%%%
% noAmenacesColumnes(+V,C)
% donada la matriu de variables,
% -> C sera la CNF que codifiqui que no s'amenecen les reines de les mateixes columnes
noAmenacesColumnes([], []).
noAmenacesColumnes(V, C):- transposadaMatriu(V, [VS|VTS]), exactamentUn(VS, FS), noAmenacesFiles(VTS, R), append(FS, R, C).

transposadaMatriu([[]|_], []).
transposadaMatriu(M, [T|TS]):- transposarColumna(M, T, RM), transposadaMatriu(RM, TS).

transposarColumna([], [], []).
transposarColumna([[H|T]|Rows], [H|Hs], [T|Ts]):- transposarColumna(Rows, Hs, Ts).


%%%%%%%%%%%%%%%%%%%%%
% minimNReines(+V,FN)
% donada la matriu de variables (inicialment d'un tauler NxN),
% -> FN sera la CNF que codifiqui que hi ha d'haver com a minim N reines al tauler
minimNReines([], []).
minimNReines([V|VS], FN):- comaminimUn(V, CNF), minimNReines(VS, R), append([CNF], R, FN).


%%%%%%%%%%%%%%%%%%%%%%%%%%%
% fesTauler(+N,+PI,+PP,V,I)
% Donat una dimensio de tauler N, unes posicions inicials PI i
% unes prohibides PP
% -> V sera el la llista de llistes variables necessaries per codificar el tauler
% -> I sera la CNF codificant posicions inicials i prohibides
fesTauler(N, PI, PP, V, I):- fixa(PI, N, PR), prohibeix(PP, N, PPR), fesMatriu(N, V), append(PR, PPR, I).
fesMatriu(N, M):- I is N*N, llista(1, I, R), trosseja(R, N, M).


%%%%%%%%%
% resol()
% Ens demana els parametres del tauler i l'estat inicial,
% codifica les restriccions del problema i en fa una formula
% que la enviem a resoldre amb el SAT solver
% i si te solucio en mostrem el tauler
% resol():-
%     ...
%     fesTauler(N,I,P,V,Ini),
%     minimNReines(V,FN),
%     ...
%     noAmenacesFiles(V,CNFfiles),
%     ...
%     noAmenacesColumnes(V,CNFcolumnes),
%     ...
%     noAmenacesDiagonals(N,CNFdiagonals),
%     ...
%     sat(...,[],...),
%     ...
%     mostraTauler(N,...).

resol1(N, I, P, V, Ini, M):- 
    fesTauler(N, I, P, V, Ini),
    minimNReines(V, FN),
    append(Ini, FN, FN1),
    noAmenacesFiles(V, CNFfiles),
    append(CNFfiles, FN1, FN2),
    noAmenacesColumnes(V,CNFcolumnes),
    append(CNFcolumnes, FN2, FN3),
    noAmenacesDiagonals(N, CNFdiagonals),
    append(CNFdiagonals, FN3, R),
    sat(R,[],M).



eliminaNegatius([], []).
eliminaNegatius([M|MS], X):- M < 0, eliminaNegatius(MS, X).
eliminaNegatius([M|MS], [M|X]):- M > 0, eliminaNegatius(MS, X).
%%%%%%%%%%%%%%%%%%%
% mostraTauler(N,M)
% donat una mida de tauler N i una llista de numeros d'1 a N*N,
% mostra el tauler posant una Q a cada posicio recorrent per files
% d'equerra a dreta.
% Per exemple:
% | ?- mostraTauler(3,[1,5,8,9...]).
% -------
% |Q| | |
% -------
% | |Q| |
% -------
% | |Q|Q|
% -------
% Fixeu-vos que li passarem els literals positius del model de la nostra
% formula.
mostraTauler(0, []).
mostraTauler(N, [L|MS]):- DN is N*N, D2 is DN -1.

mostraFilaN(F, N, _):- F > N,  write('|'), nl, !.
mostraFilaN(L, N, [L|LS]):- write('|Q'), N1 is L+1, mostraFilaN(N1, N, LS), !.
mostraFilaN(F, N, L):- write('| '), F1 is F+1, mostraFilaN(F1, N, L), !.