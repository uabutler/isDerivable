/* isDerivable
 * ===========
 * This program creates a functor, isDerivable/2, that takes two
 * arguments. The first argument is a regular expression, the second
 * is a string, both represented by atoms. If the string can be
 * derived from the regular expression, this functor returns true.
 * Otherwise, it returns false.
 *
 * As a precondition, it is assumed the regular expression is valid,
 * and that both the string and the regular expression are defined
 * only over the alphabet A = {a,b,c}. (Though this can be trivially
 * modified below.)
 *
 * For this program, A + B represents the disjuntion of two regular
 * expression, A and B, AB is the concatenation of A and B, and A*
 * is the closure of A. (A derives an expression repeated 0 or more
 * times). Program will not account
 */

/* Authors
 * =======
 * Ulysses Butler
 * Robert Maskek
 * Andrew Flynn
 * Nestor Fong
 */

/*  Base case, since the string will not contain '+' or paran,
    if this test is true, it means the regex itself is just a
    string */
isDerivable(RegEx, Input) :-
  RegEx == Input.
/*  It's nessesary to check notDerivable first to prevent infinite
    loops. If you can't derive Input from RegEx, these will all fail,
    which is enough to make the whole functor false */
isDerivable(RegEx, Input) :-
  not(notDerivable(RegEx, Input)),
  paran(RegEx, X), isDerivable(X, Input).
/*  This is the base case for star. If star is valid, regardless of
    the output, if the input is empty, the call passes. */
isDerivable(RegEx, Input) :-
  not(notDerivable(RegEx, Input)),
  star(RegEx, X),
  ((Input == '');
  (atom_concat(A, B, Input),
  A \= '',
  isDerivable(X, A),
  isDerivable(RegEx, B))).
/*  This is simple, if you can derive the string from either part of
    the disjuntion, it passes. Otherwise, it fails. */
isDerivable(RegEx, Input) :-
  not(notDerivable(RegEx, Input)),
  dis(RegEx, X, Y),
  (isDerivable(X, Input); isDerivable(Y, Input)).
/*  This also involves a lot of brute forcing. If you can split the
    string and the regular expression up into two concatenated parts
    such that a part of a regular expression can derive its
    respective part of the string, it passes. Not complicated, but
    very intensive on the part of the computer. If the whole thing
    is surrounded by parans, or is a disjuntion, it can't be a
    disjunction. */
isDerivable(RegEx, Input) :-
  not(notDerivable(RegEx, Input)),
  not(paran(RegEx, _)),
  not(dis(RegEx, _, _)),
  cat(RegEx, X, Y),
  atom_concat(A, B, Input),
  isDerivable(X, A),
  isDerivable(Y, B).

/*  Base case for a failure */
notDerivable(RegEx, Input) :-
  (letter(RegEx),
  RegEx \= Input);
  (cat(RegEx, _, _),
  Input == '').

%parentheses
/*  This looks more complicated than it actually is. Basically, it
    strips paranthesis from boths sides if it can, and returns false
    if it can't. The match functor is there to ensure the paranthesis
    being stripped off of the end actually match eachother. ex.
    (a)(b) -/-> a)(b */
paran(X, Y) :-
  atom_concat('(', A, X),
  name(A, B), match(B, 0),
  atom_concat(Y, ')', A).
/*  This is accomplished by keeping track of the paranthesis we've
    passed. At first, we've passed zero. As we progress through the
    string, if we pass an opening paran, we add one, if we pass it's
    matching closing paran, we subtract one. If we ever go below
    zero, we've passed a closing paran that wasn't opened, so we
    return false. If we get to the end, and S != 0, the match is
    somewhere later, so we've still failed */
match(I, S) :-
  S == 0,
  I == [41]. %last letter must be ')'
match([H|I], S) :-
  S >= 0,
  H == 40,
  L is S + 1,
  match(I, L).
match([H|I], S) :-
  S >= 0,
  H == 41,
  L is S - 1,
  match(I, L).
match([H|I], S) :-
  S >= 0,
  H \= 40,
  H \= 41,
  match(I, S).

%0 or more repetitions
/*  Star only applies to a single letter, or a paranthesised regular
    expression */
star(X, Y) :-
  atom_concat(Y, '*', X),
  letter(Y).
star(X, Y) :-
  atom_concat(Y, '*', X),
  paran(Y, _).

%disjunction
/*  This ordering might seem strange, but is nessesary because of
    Prolog's instantiation. Though it results in a brute force, We
    need to use X in the first call, since it's the only variable
    that's been instantiated. */
dis(X, Y, Z) :-
  atom_concat(A, Z, X),
  atom_concat(Y, '+', A),
  name(Y, B),
  gmatch(B, 0);
  atom_concat(A, Z, X),
  atom_concat(Y, ' + ', A),
  name(Y, B),
  gmatch(B, 0).
/*  gmatch/2 is a more generalized verion (general_match) of the
    match functor created above. It's not dependant on the last
    character of the string being a ')' as was needed before. It
    simply checks to make sure all parans that are opened are
    closed in the string and are closed parans were opened in the
    current string. The logic is the same as before, but with a
    modified base case */
gmatch(I, S) :-
  I == [],
  S == 0.
gmatch([H|I], S) :-
  S >= 0,
  H == 40,
  L is S + 1,
  gmatch(I, L).
gmatch([H|I], S) :-
  S >= 0,
  H == 41,
  L is S - 1,
  gmatch(I, L).
gmatch([H|I], S) :-
  S >= 0,
  H \= 40,
  H \= 41,
  gmatch(I, S).

%concatenation
/*  This will concatenate a letter or parans to another letter or
    parans. It will also concatenate a letter to the end of a
    closure */

cat(X, Y, Z) :-
  atom_concat(Y, Z, X),
  ((letter(C), atom_concat(_, C, Y)); atom_concat(_, ')', Y); atom_concat(_, '*', Y)),
  ((letter(D), atom_concat(D, _, Z)); atom_concat('(', _, Z)),
  name(Y, A),
  name(Z, B),
  gmatch(B, 0),
  gmatch(A, 0).

%letters
/* Base cases */
letter('a').
letter('b').
letter('c').
