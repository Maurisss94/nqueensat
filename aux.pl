% Passa una llista de coordenades  de tauler NxN a variables corresponents.
coordenadesAVars([],_,[]).
coordenadesAVars([(F,C)|R],N,[V|RV]):-V is (F-1)*N+C, coordenadesAVars(R,N,RV).

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
diagonals2In(D,N,[L1|L]):- D=<N,fesDiagonal(N,D,L1), D1 is D+1, diagonals2In(D1,N,L).
diagonals2In(D,N,[L1|L]):- D>N, F is D-N+1,fesDiagonalReves(F,N,N,L1), D1 is D+1, diagonals2In(D1,N,L).


%%%%%%%%%%%%%%%%%%%
% comaminimUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a minim una sigui certa.
comaminimUn([L|LS], CNF):- L > 0, append([L], LS, CNF), !.
comaminimUn([L|LS], CNF):- comaminimUn(LS,R), append([L], R, CNF).

%%%%%%%%%%%%%%%%%%%
% comamoltUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que com a molt una sigui certa.
comamoltUn(L, CNF):- negat(L, NL), combina(NL, CNF).

% negat(L, N).
% Donat una llista de variables booleans,
% -> el segon parametre sera una llista amb les variables negades.
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
llistaN(N,[_|L],R) :- llistaN(N,L,R), !.


%%%%%%%%%%%%%%%%%%%
% exactamentUn(L,CNF)
% Donat una llista de variables booleanes,
% -> el segon parametre sera la CNF que codifica que exactament una sigui certa.
exactamentUn(L, CNF):- comaminimUn(L, R), comamoltUn(L, S), append([R], S, CNF).