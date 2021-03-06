/* Covering code generator, especially for football pool systems */

/* Written and converted to GNU MathProg by NASZVADI, Peter, 199x-2017
   <vuk@cs.elte.hu> */

/*
   Looks up for minimal covering codes in the specified Hamming-space.
   Without specifying model data, by default it looks up for covering
   for a mixed covering code in Hamming-space {X, 1, 2, 3}*{X, 1}^4
   with one layer.

   Hamming space is a set of finite words with all the same length over
   a finite alphabet: the space could be decomposed to Cartesian
   products of subsets of the alphabet, e.g. the first letter of an
   element can be chosen from a 2-element set, the next from 6 letters,
   and so on.

   There is a natural metric function in these spaces: the
   Hamming-distance (hence the name, from now referred as: distance).
   The distance of two (equal-length) words is the number of different
   letter pairs in the corresponding positions.

   Covering Hamming-spaces with minimal number of spheres with given
   radius - usually difficult problem excluding special cases.

   Relationship with sports:
   Football pool system in Hungarian: "Toto'kulcs", so Toto, totogol and
   other football pool systems are usually need mixed ternary/binary
   code coverings in order to minimize loss of the gambler.

   See more at:
   https://en.wikipedia.org/wiki/Covering_code

   A tricky workaround is used:
   floor(), abs() and cosine() magic are used at 'coverings' constraints,
   because GMPL lacks proper boolean<->integer evaluation/casting.
*/

param ArgNum1,  >= 1, default 1;
param ArgNum2,  >= 1, default 1;
param ArgNum3,  >= 1, default 1;
param ArgNum4,  >= 1, default 1;
param ArgNum5,  >= 1, default 1;
param ArgNum6,  >= 1, default 1;
param ArgNum7,  >= 1, default 1;
param ArgNum8,  >= 1, default 1;
param ArgNum9,  >= 1, default 1;
param ArgNum10, >= 1, default 1;
param ArgNum11, >= 1, default 1;
param ArgNum12, >= 1, default 1;
param ArgNum13, >= 1, default 1;
/* at most 13 matches' outcomes */

param Radius, >= 1, default 1;
/* covering radius */

param Layer, >= 1, default 1;
/* each point of space must be covered at least Layer times */

set X := 0..ArgNum1 - 1 cross 0..ArgNum2 - 1 cross 0..ArgNum3 - 1 cross
         0..ArgNum4 - 1 cross 0..ArgNum5 - 1 cross 0..ArgNum6 - 1 cross
         0..ArgNum7 - 1 cross 0..ArgNum8 - 1 cross 0..ArgNum9 - 1 cross
         0..ArgNum10 - 1 cross 0..ArgNum11 - 1 cross 0..ArgNum12 - 1 cross
         0..ArgNum13 - 1;
/* the Hamming-space generated by the Cartesian-products of sets
   with elements ArgNum[n] */

var x{X}, integer, >=0;
/* denotes each point's amount of containing covering sets */

var objvalue;

s.t. coverings{(i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13) in X}:
        sum{(j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13) in X:
            floor(abs(cos(i1 - j1)))   + floor(abs(cos(i2 - j2))) +
            floor(abs(cos(i3 - j3)))   + floor(abs(cos(i4 - j4))) +
            floor(abs(cos(i5 - j5)))   + floor(abs(cos(i6 - j6))) +
            floor(abs(cos(i7 - j7)))   + floor(abs(cos(i8 - j8))) +
            floor(abs(cos(i9 - j9)))   + floor(abs(cos(i10 - j10))) +
            floor(abs(cos(i11 - j11))) + floor(abs(cos(i12 - j12))) +
            floor(abs(cos(i13 - j13))) >= 13 - Radius
        } x[j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13] >= Layer;
/* covering constraints, select at least 'Layer' amount of spheres that cover
   (i1,i2,...) and has radius 'Radius' */

s.t. oneisset: x[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] >= 1;
/* this does not violate symmetry nor excludes important solutions but
   boosts the solving process */

s.t. objc: sum{(i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13) in X}
        x[i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13] = objvalue;
/* the total number of pools (covering sets) */

minimize obj: objvalue;
/* Also 'objc' could be used directly instead of 'obj', but for
   experiments, it is useful to set up additional constraints for
   introduced objvalue variable */

solve;

printf 'Solution: %s\nRadius: %s\nLayer: %s\n',
       objvalue.val, Radius, Layer;
/* report important scalars */

printf 'Selected bets:\n';
for{(i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13) in X:
    x[i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13]}{
    printf ' Times %s:',
        x[i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13].val;
    printf '%s', if ArgNum1 == 1 then '' else ' ' & if i1 then i1 else 'X';
    printf '%s', if ArgNum2 == 1 then '' else '-' & if i2 then i2 else 'X';
    printf '%s', if ArgNum3 == 1 then '' else '-' & if i3 then i3 else 'X';
    printf '%s', if ArgNum4 == 1 then '' else '-' & if i4 then i4 else 'X';
    printf '%s', if ArgNum5 == 1 then '' else '-' & if i5 then i5 else 'X';
    printf '%s', if ArgNum6 == 1 then '' else '-' & if i6 then i6 else 'X';
    printf '%s', if ArgNum7 == 1 then '' else '-' & if i7 then i7 else 'X';
    printf '%s', if ArgNum8 == 1 then '' else '-' & if i8 then i8 else 'X';
    printf '%s', if ArgNum9 == 1 then '' else '-' & if i9 then i9 else 'X';
    printf '%s', if ArgNum10 == 1 then '' else '-' & if i10 then i10 else 'X';
    printf '%s', if ArgNum11 == 1 then '' else '-' & if i11 then i11 else 'X';
    printf '%s', if ArgNum12 == 1 then '' else '-' & if i12 then i12 else 'X';
    printf '%s', if ArgNum13 == 1 then '' else '-' & if i13 then i13 else 'X';
    printf '\n';
}
/* pretty-print a generated football pool system (covering code) */

data;

param ArgNum1 := 4;
param ArgNum2 := 2;
param ArgNum3 := 2;
param ArgNum4 := 2;
param ArgNum5 := 2;

end;
