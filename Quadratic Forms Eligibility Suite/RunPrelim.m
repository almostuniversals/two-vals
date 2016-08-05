// CREDIT FOR THIS FILE GOES TO Jeremy Rouse
// This MAGMA script does preprocessing
// on a list of quadratic forms. It
// outputs one file for each form with
// of the data necessary for the
// verification of universality.
// It also writes a log file (formnumber.log)
// with nicely formatted data about the form.
// This files takes an argument, giving the index
// of the form to be tried in an appropriate input file.

// The file "quatver.txt" should contain
// a list of Gram matrices (half-integral off-diagonal entries are OK)
// called quatver.

// Correct command line syntax for calling this script
// might be the following
// magma mmm:=2 prep.txt
// (no spaces anywhere in mmm:=2)

// This script will do all pre-processing on the quadratic form
// including computing the Eisenstein lower bound and
// the cusp constant. The results are output to the file (formnum)data.out.



// output filename will be (mmm)data.out
/*
output to this file should be one line with each data entry.
The following is the necessary data:
1. The form number
2. The level
3. The character
4. The anisotropic primes (list)
5. The ratio of the Eisenstein bound and cuspidal constant (the F4
bound)
6. The split local cover number d
7. The ternary summand (for ease of parsing, we multiply it by 2, so
all the things in the list are definitely integers), a list of 9 integers.
*/

// The log file is a text file that
// receives status reports and errors

MQ := RMatrixSpace(RationalField(), 4, 4);

// The file quatver.txt should be loaded on the command line

load "quatver.txt";
M := MQ ! quatver[mmm];

// In order for mutual recursion to happen, we must
// declare the relevant functions ahead of time.

forward LocalDensity, LocalGoodDensity, LocalZeroDensity,
LocalBadDensity, GetLocal;

// Relevant global declarations

Z := Integers();
Q := Rationals();
R := RealField(50);
RR := RealField(50);

/* INDEX FUNCTION */

// This function computes the index of Gamma_0(N) in Gamma_0(1).
// This is used to determine the precision necessary for
// the modular form computations

function IndexValue(N)
  L := Factorization(N);
  index := N;
  for n in [1..#L] do
    index := index*(L[n][1]+1)/(L[n][1]);
  end for;
  return Floor(index);
end function;

/* END INDEX FUNCTION */

// Determine the level of the quadratic form Q.
/*
The level of Q is the minimal number N such that N * B^(-1) is a
matrix with integer entries and even diagonal entries; here B is twice
the matrix associated to Q.  So for example, the four-squares form has
corresponding matrix B=diag[2,2,2,2]; its inverse is then [1/2,1/2,1/2,1/2],
so N=4. This follows from Proposition 10.6c of Iwaniec.
*/

/* LEVEL FUNCTION */

function LevelOfQuadForm(B)
  if Ncols(B) eq 3 then
    Binv := B^(-1);
    N := LCM([Denominator(x) : x in Eltseq(Binv)]);
    return 2*N;
  end if;
  if Ncols(B) eq 4 then
    Binv := B^(-1);
    N := 1;
    l := LCM([Denominator(x) : x in Eltseq(N*Binv)]);
    N := N*l;
    n := NumberOfRows(B);
    m := GCD([Numerator(N*Binv[i,i]) : i in [1..n]]);
    if IsOdd(m) then
      N := N*2;
    end if;
    return Integers()!N;
  end if;
end function;

/* END LEVEL FUNCTION */

/* CUSPIDAL CONSTANT FUNCTION */

/* CUSPIDAL CONSTANT FUNCTION */

///////////////////////////////////////////////////////////////////////
// Compute the cuspidal constant of any positive definite quaternary
// integer-valued quadratic form, given here by the matrix of 2*Q.
// (Note: This is really the same as the integer-matrix form, 
// but at a lower level, since theta_{2Q}(z) = theta_{Q}(2z).) =)
// This version reads the pre-computed Theta series, Eisenstein series
// and coefficient bound
///////////////////////////////////////////////////////////////////////
function compute_cusp_constant(QQ,T,Eis,coeff_bound)

// TIMING: Set the current time
t := Cputime();

// DIAGNOSTIC
//print "Using the matrix 2*Q =",QQ;

// Some useful definitions -- used in finding the determinant and level
Q4 := RMatrixSpace(Rationals(),4,4);
Z4 := RMatrixSpace(IntegerRing(),4,4);

// Make the appropriate (quadratic) character and level
N := LevelOfQuadForm(Q4!QQ);  // This is the level
D := Determinant(Z4!QQ);      // This is the determinant (since QQ is even-dim'l)
if IsSquare(D) then      // This deals with Magma's unhappiness about square discriminants... =(
  eps_top := 1;
else 
  eps_top := FundamentalDiscriminant(D);
end if;
eps := KroneckerCharacter(eps_top, RationalField());
//print "The form Q has level", N, "and determinant", D/16;


M2 := ModularForms(DirichletGroup(N) ! eps);
S2 := CuspidalSubspace(M2);
Dim_S2 := Dimension(S2);
//print "The dimension of the cuspidal subspace is ", Dim_S2;
precision := PrecisionBound(S2);
//print "Need the precision: ", precision, "to uniquely identify a cusp form.";
/*
precision := 8*Dimension(S2);                      // TO DO: Need to adjust this, as well as the m_range below!
print "Using precision: ", precision;
*/

// TIMING: Check the time taken up to this point, and reset the time.
//print "TIMING: Time to setup the spaces of modular forms = ", Cputime(t), " seconds.";
t := Cputime();


// Return with a constant of zero if there is no cuspidal subspace! =)
if Dim_S2 eq 0 then
  //print "The cuspidal space is 0-dim'l, so are no cusp forms!";
  //print "\n This gives the overall cuspidal constant of:", 0;
  return 0;
end if;



// Make a bound on the degree of of newforms considered...based on the class number:
// ---------------------------------------------------------------------------------
//degree_bound := 2 * #GenusRepresentatives(LatticeWithGram(QQ));   // This was a good idea, but it failed. =(
//degree_bound := 100;   // This now gives a computationally meaningful bound! =)
degree_bound := 200000;   // This now gives a meaningless bound! =)


// Make a list of newforms, and their levels:
// ------------------------------------------
big_oldform_d_list := [d : d in Divisors(N div Conductor(eps))];
level_list := [* *];
form_list := [* *];
for r in [q : q in Divisors(N) | q mod Conductor(eps) eq 0] do
  // Make the new character (which carries the level)
  eps_r := DirichletGroup(r) ! eps;
  //  M_d := ModularForms(r);    // This uses only the trivial character
  M_r := ModularForms(eps_r);    // This uses the correct quadratic character, but it's too big to finish! =(
  //  SetPrecision(S_r, precision+1);   // Set the printing precision
  S_r := CuspidalSubspace(M_r);
  PrintFile(LOGFILE,Sprintf("Computing newforms of level %o.",r));
  NewNum_r := NumberOfNewformClasses(S_r);             // THIS TAKES A LONG TIME! =(
  //print "There are ", NewNum_r, " classes of (cuspidal) newforms of level", r;
  for i in [1..NewNum_r] do
    tmp_newform := Newform(S_r, i);
    PrintFile(LOGFILE,Sprintf("Newform class %o has size %o.",i,Degree(tmp_newform)));
    if Degree(tmp_newform) le degree_bound then   // OLD COMMENT: Here we filter newforms with degree larger than the class number!
      level_list := Append(level_list, r);
      form_list := Append(form_list, tmp_newform);
      //print "Class ", i , ": ", CoefficientField(tmp_newform);
    else 
      //print "Skipping class ", i , "... since its degree = ",
      Degree(CoefficientField(tmp_newform)), ">", degree_bound;
      quit;
    end if;
  end for;
//print "  form_list = ", form_list;
end for;
//print " Using big_oldform_d_list =", big_oldform_d_list;
//print " Using level_list =", level_list;

// Precompute the allowed_j_lists for each d, and make d's which have some assoicated newform:
// -------------------------------------------------------------------------------------------
allowed_j_list_vec := [ ];
oldform_d_list := [ ];

for d in big_oldform_d_list do

  // Compute the allowed indices j for this new/oldform lift
  //print " ";
  //print "Starting the computation for the old/newform lift d =", d;
  allowed_j_list := [j : j in [1..#form_list] | N mod (d * level_list[j]) eq 0];
  //print "The allowed_j_list is", allowed_j_list;

  // Add it to the vector if it's not empty    
  if not IsEmpty(allowed_j_list) then
    oldform_d_list := Append(oldform_d_list, d);
    allowed_j_list_vec := Append(allowed_j_list_vec, allowed_j_list);
  end if;
  // *********  TO DO:  **********
  // If there are no allowed forms, then we should remove d from the list!!!
  // Also, we'll need to modify the level list too...
  // This will save us the trouble of protecting against this all the time!!! =)
  // *****************************

end for;
//print " Using oldform_d_list =", oldform_d_list;

// Precompute a list of eligible coefficients to use which allows us to use the fewest number of primes:
// -----------------------------------------------------------------------------------------------------
possible_primes_500 := [];
p := 1;
while #possible_primes_500 lt 500 do                // Precompute 50 possible primes to try. =)
  p := NextPrime(p);
  if N mod p ne 0 then
    possible_primes_500 := Append(possible_primes_500, p);
  end if;
end while;
//print "The list of possible primes p prime to N = ", N, " is ", possible_primes_500;



// Add a minimal set of coefficients (prime-by-prime) to span the (d=1) eigenspace:
// --------------------------------------------------------------------------------
newform__p_coeff_list := [ [* *] : j in [1.. #form_list] ];   // one list for each newform, then the primes for each are stored according to prime_seq. =)
Big_EigenRows_Matrix_list := [* *];
N_min := Conductor(eps);  // Conductor of the level character

good_mm_list_vec := [];
Big_EigenRows_Matrix_list := [* *];

// Run through all possible d's, and construct the minimal set of coefficients.
for ind in [1..#oldform_d_list] do  

  // Some initial conditions 
  emptymatrixflag := true;
  r := Cputime();
  d := oldform_d_list[ind];                   // This should be d=1 
  PrintFile(LOGFILE,Sprintf("Finding minimal coefficients for d = %o.",d));
  allowed_j_list := allowed_j_list_vec[ind];  // This gives the full list!
  further_lift_num := N div (d * N_min);
  last_rank := 0;
  good_mm_list := [ ];
  old_eligible_coeff_seq := [ ];
  k := 1;  // prime index in possible_primes_50
  rank_is_full_flag := false;


  // Find the minimal set of coefficients
  while rank_is_full_flag eq false do

    p := possible_primes_500[k];

    // Check if that prime hasn't been computed already
    if #newform__p_coeff_list[1] lt k then
      PrintFile(LOGFILE,Sprintf("Computing newform coefficients at p = %o.",p));
      // Compute all p-power coefficients:
      // ---------------------------------
      for j in [1.. #form_list] do

        // Compute the p-th eigenvalue
        //print "Computing the coefficient at ", p, "for the newform at j = ", j;
        newform__p_coeff_list[j] := Append(newform__p_coeff_list[j], [ Coefficient(form_list[j], p) ]); // Keeps a list of p-powers, starting at p.  
        dirchar := DirichletCharacter(form_list[j]);

        // Compute the p-power coefficients
        for r in [2 .. Floor(Log(coeff_bound)/Log(p))] do
          //print " Computing the coefficient for newform ", j, " at p^r = ", p, "^", r, " = ", p^r;
          if r eq 2 then
            p_r__coeff := newform__p_coeff_list[j][k][1]^2 - dirchar(p) * p;
          else
            p_r__coeff := newform__p_coeff_list[j][k][1] * newform__p_coeff_list[j][k][r-1] - dirchar(p) * p * newform__p_coeff_list[j][k][r-2];
          end if;

          newform__p_coeff_list[j][k] := Append(newform__p_coeff_list[j][k], p_r__coeff); 
        end for;
    
      end for;

    end if;


    // TO DO: Then check if the prime extends the current coefficient field at all.


    // Make the additional set of coefficients we need to test  (They're m1, not d*m1) 
    possible_prime_powers := [p^i : i in [1 .. Floor(Log(coeff_bound/d)/Log(p))]];   // Make p-powers up to coeff_bound 
    if old_eligible_coeff_seq eq [] then
      old_eligible_coeff_seq := [1];
      Append(~possible_prime_powers,1);
    end if;
    new_coeff_seq := [i*j : i in old_eligible_coeff_seq, j in possible_prime_powers | i*j lt coeff_bound/d ];
    old_eligible_coeff_seq := Sort(old_eligible_coeff_seq cat new_coeff_seq);

    // Add these new rows to the Big_Eigenrows_Matrix:
    // -----------------------------------------------
    //print "About to compute the rows at the coefficients: ", new_coeff_seq;

    // Loop through all of our possible coefficients to make the Big_Eigenrows_Matrix
    for m1 in new_coeff_seq do
      mm := d * m1;

      // Make the mm-th row vector
      s := Cputime();
      tmp_coeff_seq := [];
      for j in allowed_j_list do

        // Compute the m1 coefficient of the j-th newform
        if m1 eq 1 then
          new_tmp_coeff :=  CoefficientField(form_list[j]) ! 1;
        else    
          new_tmp_coeff := &*[newform__p_coeff_list[j][Index(possible_primes_500, q)][Valuation(m1, q)] : q in possible_primes_500 | Valuation(m1, q) ge 1];
        end if;

        tmp_coeff_seq := tmp_coeff_seq cat ElementToSequence(new_tmp_coeff);
      end for;

      tmp_rowvec := RMatrixSpace(RationalField(), 1, #tmp_coeff_seq) ! tmp_coeff_seq;

      // Add it to the big row matrix, and to the list of (good_mm) row indices
      if emptymatrixflag eq true then
        Big_EigenRows_Matrix := tmp_rowvec;
        emptymatrixflag := false;
      else
        Big_EigenRows_Matrix := VerticalJoin(Big_EigenRows_Matrix, tmp_rowvec);
      end if;
      good_mm_list := good_mm_list cat [mm];


    end for;

    // Compute the rank modulo three random primes p > 10000, and remove rows which don't contribute to these ranks.
    // -------------------------------------------------------------------------------------------------------------
    s := Cputime();
    old_size := NumberOfRows(Big_EigenRows_Matrix);

    PrintFile(LOGFILE,Sprintf("The big matrix now has %o rows.",old_size));

    // Make a list of random primes
    rand_prime_list := [];
    while #rand_prime_list lt 3 do
    rp := RandomPrime(25);
      if rp gt 100000 then
        rand_prime_list := Append(rand_prime_list, rp);
      end if;
    end while;


    // Run through our random primes to do the rank checking
    for rp in rand_prime_list do
      PrintFile(LOGFILE,Sprintf("Rank checking with p = %o",rp));
      // Find the bad rows in the mod p matrix
      BEMp := ChangeRing(Big_EigenRows_Matrix, FiniteField(rp));
      tmp_echelon := EchelonForm(Transpose(BEMp));  // The columns with pivots index the rows to keep! =)
      good_indices := [];
      for i in [1..NumberOfRows(tmp_echelon)] do
        pivot_flag := false;
        for j in [1..NumberOfColumns(tmp_echelon)] do
          if (tmp_echelon[i,j] ne 0) and (pivot_flag eq false) then
            pivot_flag := true;
            good_indices := Append(good_indices, j);
          end if;
        end for;
      end for;

      // Make a new Big_EigenRows_Matrix and good_mm_list using the good indices above
      BEM2 := Matrix([Big_EigenRows_Matrix[i] : i in good_indices]);
      good_mm2 := [good_mm_list[i] : i in good_indices];
      Big_EigenRows_Matrix := BEM2;
      good_mm_list := good_mm2;
      delete BEM2, good_mm2;

      new_size := NumberOfRows(Big_EigenRows_Matrix);
      PrintFile(LOGFILE,Sprintf("Matrix now has %o rows.",new_size));

    end for;


    // Check if we're done! =)
    PrintFile(LOGFILE,Sprintf("Matrix has %o columns.",Ncols(Big_EigenRows_Matrix)));
    if Nrows(Big_EigenRows_Matrix) eq Ncols(Big_EigenRows_Matrix) then
      rank_is_full_flag := true;
    end if;


    // Status report and increment

    k := k + 1;



  end while;
  k:= k - 1;



  // Append these coefficients to the list (for each d)
  good_mm_list_vec := Append(good_mm_list_vec, good_mm_list);
  //print "good_mm_list_vec = ", good_mm_list_vec;

  // Append these matrices to the list (for each d)
  Big_EigenRows_Matrix_list := Append(Big_EigenRows_Matrix_list, Big_EigenRows_Matrix);
  PrintFile(LOGFILE,Sprintf("We're done with d = %o!",d));
end for;


// Make a list of primes we actually use  (THIS IS SUPERFLUOUS, BUT USED LATER!)
prime_seq := possible_primes_500[1..#newform__p_coeff_list[1]];


//  coeff_seq := Sort(old_eligible_coeff_seq);

// Compute the prime-power coefficients at p|N  (where N is the big level):
// ------------------------------------------------------------------------
PrintFile(LOGFILE,"Computing coefficients at primes dividing the level.");
D_LCM := LCM(oldform_d_list);
N_prime_seq := PrimeDivisors(D_LCM);
N_newform__p_coeff_list := [ [* *] : j in [1.. #form_list] ];   // one list for each newform, then the primes for each are stored according to prime_seq. =)
for p in N_prime_seq do
  k := Index(N_prime_seq, p);     // Index of p in prime_seq
  for j in [1.. #form_list] do

    // Useful definitions
    N_j := level_list[j];
    bad_primes_j := PrimeDivisors(N_j);


    // Compute the p-th eigenvalue
    N_newform__p_coeff_list[j] := Append(N_newform__p_coeff_list[j], [ Coefficient(form_list[j], p) ]); // Keeps a list of p-powers, starting at p.  
    dirchar := DirichletCharacter(form_list[j]);

    // Compute the p-power coefficients
    for r in [2 .. Valuation(D_LCM,p)] do
      //print " Computing the coefficient for newform ", j, " at p^r = ", p, "^", r, " = ", p^r;
      if p in bad_primes_j then
        p_r__coeff := N_newform__p_coeff_list[j][k][1] ^ r;
      else
        if r eq 2 then
          p_r__coeff := N_newform__p_coeff_list[j][k][1]^2 - dirchar(p) * p;
        else
          p_r__coeff := N_newform__p_coeff_list[j][k][1] * N_newform__p_coeff_list[j][k][r-1] - dirchar(p) * p * N_newform__p_coeff_list[j][k][r-2];
        end if;
      end if;

      // Append it to the list
      N_newform__p_coeff_list[j][k] := Append(N_newform__p_coeff_list[j][k], p_r__coeff); 
    end for;

  end for;
end for;
//print "The table of newform coefficients at p|N is: ", newform__p_coeff_list;




// Make the theta series and its Eisenstein and cuspidal parts
// -----------------------------------------------------------

// Compute the precision from the good_mm_list_vec
precision := 0;
for good_mm_list in good_mm_list_vec do
  if not IsEmpty(good_mm_list) then
    precision := Max(precision, Max(good_mm_list));
  end if;
end for;
precision := precision + 1;

// Compute the set of allowed Fourier coefficients
Allowed_coefficients_set := {};
for good_mm_list in good_mm_list_vec do
  Allowed_coefficients_set := Allowed_coefficients_set join Seqset(good_mm_list);
end for;
Allowed_coefficients_list := Setseq(Allowed_coefficients_set);

// Make the Cusp form, and set it as the cuspidal remainder.
Cusp_vec := [Coefficient(T,m) - Coefficient(Eis, m) : m in [0..precision]];
PS<q> := PowerSeriesRing(Rationals());
Cuspidal_Theta := (PS ! Cusp_vec) + O(q^#Cusp_vec);
remaining_cuspidal_theta := Cuspidal_Theta;

// DIAGNOSTIC -- Print the first 20 terms of Theta(z), E(z), and f(z).
//print "";
//print "Theta(z) =", (PS ! Theta_vec) + O(q^20);
//print "E(z) =", (PS ! Eis_vec) + O(q^20);
//print "f(z) =", (PS ! Cusp_vec) + O(q^20);
//print "";

// Kill all coefficients of Theta(z) not in the allowed set (so the sum is zero at the end, since we only update these!).
for mm in (Seqset([1..precision]) diff Allowed_coefficients_set) do
  remaining_cuspidal_theta := remaining_cuspidal_theta - Coefficient(remaining_cuspidal_theta,mm) * q^mm;
end for;
//print "The truncated theta function (at allowed coefficients) is: ", remaining_cuspidal_theta;


// Find the new/oldform decomposition for each possible oldform lift f(z) -> f(dz):
// --------------------------------------------------------------------------------
oldform_coefficient_list := [* *];

//for d in oldform_d_list do
for ind in [1..#oldform_d_list] do

  // Some precomputed info =)
  d := oldform_d_list[ind];
  PrintFile(LOGFILE,Sprintf("Working on decomposition of d = %o piece.",d));
  allowed_j_list := allowed_j_list_vec[ind];
  Big_EigenRows_Matrix := Big_EigenRows_Matrix_list[ind];   // NOTE: THIS MAY SLOW IS DOWN SINCE WE NEED TO COPY THE MATRIX AGAIN!?!
  m_range := good_mm_list_vec[ind];
  m_range_set := Seqset(m_range);

  // TIMING: Reset the time.
  t := Cputime();


  // Compute the dimension of the new/oldform space for this d
  d_dim := &+[Degree(form_list[j]) : j in allowed_j_list];
  //print "Using d =", d, "generates a", d_dim, "cuspidal subspace.";


  // Make the direct sum of the trace matrices (only for allowed indices j) 
  trace_matrix_list := [* *];
  for j in allowed_j_list do
    PrintFile(LOGFILE,Sprintf("Building trace matrix for newform %o.",j));
    f := form_list[j];

    // Use the basis [1] for the rationals, and the powers of a generator otherwise...
    K := CoefficientField(form_list[j]);
    deg := Degree(K);
    if (deg eq 1) then  
      a := 1;
      temp_trace_matrix := MatrixRing(RationalField(), 1) ! [1];
    else
      K<a> := CoefficientField(form_list[j]);
      temp_trace_matrix := ZeroMatrix(RationalField(), deg, deg);  

      // Make the trace matrix efficiently. =)
      tmp_a_pow := K ! 1;
      for i_plus_j in [2..2*deg] do

        // Compute the trace
        tmp_a_trace := Trace(tmp_a_pow);

        // Fill in the reverse diagonals
        for i in [Max(1, i_plus_j - deg) .. Min(deg, i_plus_j - 1)] do
          j1 := i_plus_j - i;
          temp_trace_matrix[i,j1] := tmp_a_trace;
        end for;

        // Increment the element
        tmp_a_pow := tmp_a_pow * a;

      end for;
//Old Way:   temp_trace_matrix := MatrixRing(RationalField(), deg) ! [Trace(a^((i-1)+(j-1))): i, j in [1..deg] | i le j];
    end if;


    trace_matrix_list := Append(trace_matrix_list, temp_trace_matrix);
    PrintFile(LOGFILE,"Done!");
  end for;

  Big_Trace_Matrix := trace_matrix_list[1];
  PrintFile(LOGFILE,"Building big trace matrix.");
  for j in [2..#trace_matrix_list] do
    Big_Trace_Matrix := DirectSum(Big_Trace_Matrix ,trace_matrix_list[j]);
  end for;  
  //print "  The trace matrix has", Nrows(Big_Trace_Matrix), "rows and ", Ncols(Big_Trace_Matrix), "columns.";


// New way - Don't multiply the matrices - solve two systems!
  new_coeff_vec := RMatrixSpace(RationalField(), #m_range, 1) ! [Coefficient(remaining_cuspidal_theta, m) : m in m_range];
  b := new_coeff_vec;

  PrintFile(LOGFILE,"Solving the eigen matrix linear system!");
  t := Cputime();
  ok1, x1 := IsConsistent(Transpose(Big_EigenRows_Matrix), Transpose(b));
  if not ok1 then
    error "The system is not consistent... =(";
    quit;
  end if;
  PrintFile(LOGFILE,"Solving the trace matrix linear system!");
  ok2, x2 := IsConsistent(Transpose(Big_Trace_Matrix), x1);
  if not ok2 then
    error "The system is not consistent... =(";
    quit;
  end if;
  x := x2; 
  PrintFile(LOGFILE,Sprintf("Done! Time taken was %o",Cputime(t)));  

  x_seq := ElementToSequence(x);
  //print "  Is the system consistent?", ok;
  PrintFile(LOGFILE,"It worked!");

  // Break x up into coefficients for each Galois conjugacy class
  // -------------------------------------------------------------
  other_x := x_seq;
  coefficient_list := [* *];
  for j in [1..#form_list] do
    f := form_list[j];
    K := CoefficientField(f);
    deg := Degree(f);

    // Write the coefficients we found, with zeros elsewhere.
    if j in allowed_j_list then
      first_x := [other_x[i] : i in [1..deg]];
      other_x := [other_x[i] : i in [deg+1..#other_x]];
      coefficient_list := Append(coefficient_list, K ! first_x);
    else
      coefficient_list := Append(coefficient_list, K ! [0 : i in [1..deg]]);
    end if;

  end for;

  // Append the current coefficient_list to the cumulative oldform_coefficient_list
  oldform_coefficient_list := Append(oldform_coefficient_list, <coefficient_list,d>);
  //print "  We have the coefficient vector", coefficient_list;


  // Find what's left over when we subtract the old/newform part for this d-value
  // -----------------------------------------------------------------------------

  // Make the big matrix used to find any rational coefficient
  BB := x * Big_Trace_Matrix;

  // Make our newform component as a power series
  new_component_vec := [ 0 ];

//print " ************  Subtracting off some Fourier coefficients  *****************";
//print "d = ", d;
//print "m_range_set = ", m_range_set;

  // MAIN LOOP for subtracting the newform components
  for mm in [1..precision] do
    tmp_num_seq := [0];

    // Only compute coefficients for allowed entries! =)
    if (mm mod d eq 0) and (mm in Allowed_coefficients_set) then

      // Don't recompute the answer for elements of M_d, instead steal them to make the answer zero. =)
      if mm in m_range_set then
        tmp_num_seq := [ Coefficient(remaining_cuspidal_theta, mm) ];   // Using mm+1 since the 1st entry is the 0-th Fourier coefficient!
      else
 
        // TIMING: Set the time
        s := Cputime();

        // Make the rational eigenform coefficient (column) vector for each coefficient mm
        tmp_coeff_seq := [];
        for j in allowed_j_list do

          // Compute the m1 coefficient of the j-th newform -- NOW INCLUDING PRIMES AT EACH LEVEL! =0
	  // ----------------------------------------------------------------------------------------
  	  m1 := mm div d;
          m1_bad := GCD(m1, N);
          m1_good := m1 div m1_bad;
          assert (GCD(N, m1_good) eq 1);   // Sanity check! =)

          // Compute the part away from N
          if m1_good eq 1 then
            new_tmp_coeff :=  CoefficientField(form_list[j]) ! 1;
          else    
            new_tmp_coeff := &*[newform__p_coeff_list[j][Index(prime_seq, p)][Valuation(m1_good, p)] : p in prime_seq | Valuation(m1_good, p) ge 1];
          end if;

          // Compute the part at N
          if m1_bad eq 1 then
            new_tmp_coeff := new_tmp_coeff * CoefficientField(form_list[j]) ! 1;
          else    
            new_tmp_coeff := new_tmp_coeff * &*[N_newform__p_coeff_list[j][Index(N_prime_seq, p)][Valuation(m1_bad, p)] : p in N_prime_seq | Valuation(m1_bad, p) ge 1];
          end if;


          // Append it to the others.
          tmp_coeff_seq := tmp_coeff_seq cat ElementToSequence(new_tmp_coeff);

        end for;
        tmp_colvec := RMatrixSpace(RationalField(), #tmp_coeff_seq, 1) ! tmp_coeff_seq;

        // Make the new_coefficient at mm
        tmp_num_matrix := BB * tmp_colvec;
        //print "New coefficient at ", mm, " = ", tmp_num_matrix;
        tmp_num_seq := ElementToSequence(tmp_num_matrix);

      end if;

    end if;
    new_component_vec := new_component_vec cat tmp_num_seq;
  end for;

  // Subtract it from the remaining cuspidal theta
  newform_component := PS ! new_component_vec;
  remaining_cuspidal_theta := remaining_cuspidal_theta - newform_component;
  //print "  The remaining cuspidal component after removing the oldforms at", d, " is:";
  //print remaining_cuspidal_theta;
end for;
PrintFile(LOGFILE,"The full decomposition is complete!");

// Print the newforms, their levels, and their coefficients

// Compute the overall cuspidal constant! =)
total_cusp_constant := 0;
formcount := 0;
for oldform_coefficient_list_by_d in oldform_coefficient_list do 
  curd := oldform_coefficient_list_by_d[2];
  for c in oldform_coefficient_list_by_d[1] do
    clist := Conjugates(c);
/*
    for mmm in [1..#clist] do
      PrintFile(LOGFILE,Sprintf("Entry %o in newform class has coefficient %o.\n",mmm,ComplexField(10)!clist[mmm]));
    end for;
*/
    r1, r2 := Signature(Parent(c));    // Finds the number of real and complex embeddings
                                       // Note: This should be the same as the embeddings of the newform, 
                                       //       even if the coefficient is in a smaller number field, 
                                       //       since we coerced it into the same ring.  EXPLICITLY CHECK THIS!!!

    // Make the absolute values
    if (r1 eq 1) and (r2 eq 0) then      // Deal with the rational field separately since Magma is unhappy... =(
      c_embedding_sizes := [Abs(c)];
    else
      c_embedding_sizes := AbsoluteValues(c);
    end if;
    c_real := c_embedding_sizes[1..r1];
    c_complex := c_embedding_sizes[r1+1..r2];

    // Compute the sum of all absolute values (with multiplicity)
    c_cusp_const := &+c_real;
    c_cusp_const := c_cusp_const + 2 * &+c_complex;
    c_cusp_const := c_cusp_const/Sqrt(curd); 
    formcount := formcount + 1;
    // Print the computed value, and add it to the overall cuspidal constant
    //print "We computed the constant for c =", c, "as", c_cusp_const;
    total_cusp_constant := total_cusp_constant + c_cusp_const;

  end for;
  //print "";
end for;

return total_cusp_constant;
end function;


/* END CUSPIDAL CONSTANT FUNCTION */

/* ANISOTROPIC PRIMES FUNCTIONS */

/* HILBERT SYMBOL */

// This is the usual Hilbert symbol for Q. The computation
// comes from Serre's A Course in Arithmetic Theorem III.1

function HilbertSymbol(a,b,p)
  if p gt 2 then
    ep := Floor((p-1)/2);
    alpha := Valuation(a,p);
    beta := Valuation(b,p);
    u := a/(p^alpha);
    v := b/(p^beta);
    F := FiniteField(p);
    u := F ! u;
    v := F ! v;
    u := Integers() ! u;
    v := Integers() ! v;
    ret := ((-1)^(alpha*beta*ep));
    ret := ret*LegendreSymbol(u,p)^(beta)*LegendreSymbol(v,p)^(alpha);
  end if;
  if p eq 2 then
    alpha := Valuation(a,p);
    beta := Valuation(b,p);
    u := a/(p^alpha);
    v := b/(p^beta);
    F := Integers(8);
    u := F ! u;
    v := F ! v;
    u := Integers() ! u;
    v := Integers() ! v;
    eu := Floor((u-1)/2);
    ev := Floor((v-1)/2);
    wu := Floor((u^2-1)/8);
    wv := Floor((v^2-1)/8);
    retexp := eu*ev + alpha*wv + beta*wu;
    ret := (-1)^(retexp);
  end if;
  return ret;
end function;

/* P-ADIC SQUARE FUNCTION */

// This function takes a rational and a prime p and determines if that
// rational is a square modulo that prime. The algorithm comes from
// Serre's A Course in Arithmetic Theorem II.3 and Theorem II.4

function IsPAdicSquare(r,p);
  if p gt 2 then
    v := Valuation(r,p);
    r := r/(p^v);
    F := FiniteField(p);
    r := F ! r;
    r := Integers() ! r;
    l := LegendreSymbol(r,p);
    if l eq 1 and v mod 2 eq 0 then
      ret := true;
    else
      ret := false;
    end if;
  end if;
  if p eq 2 then
    v := Valuation(r,p);
    r := r/(p^v);
    F := Integers(8);
    r := F ! r;
    r := Integers() ! r;
    if r eq 1 and v mod 2 eq 0 then
      ret := true;
    else
      ret := false;
    end if;
  end if;
  return ret;
end function;

// This function determines whether or not M is anisotropic at p.
// A form is anisotropic if f(x1,x2,x3,x4) = 0 implies x1=x2=x3=x4 in
// Z_p.


/* ANISOTROPIC PRIMES FUNCTION */

function aniso(M)
  ret := [];
  N := LevelOfQuadForm(2*M);
  F := Factorization(N);
  Mold := M;
  for n in [1..#F] do
    // Use our routines
    p := F[n][1];
    //printf "Testing anisotropy at p = %o.\n",p;
    M := GetLocal(Mold,p);
    //printf "Local splitting is %o.\n",M;

    if p eq 2 then
      if Ncols(M) eq 4 then
        for i in [1..3] do
          if M[i,i+1] ne 0 then
            alpha := M[i,i];
            beta := M[i,i+1];
            gamma := M[i+1,i+1];
            if (alpha ne 0) then
              M[i,i] := alpha^3;
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i+1,i+1] := alpha^2*gamma - alpha*beta^2;
            end if;
            if (alpha eq 0) and (gamma ne 0) then
              M[i,i] := gamma^3;
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i+1,i+1] := alpha*gamma^2 - gamma*beta^2;
            end if;
            if (alpha eq 0) and (gamma eq 0) then
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i,i] := 2*beta;
              M[i+1,i+1] := -2*beta;
            end if;
          end if;
        end for;
      end if;
      if Ncols(M) eq 3 then
        for i in [1..2] do
          if M[i,i+1] ne 0 then
            alpha := M[i,i];
            beta := M[i,i+1];
            gamma := M[i+1,i+1];
            if (alpha ne 0) then
              M[i,i] := alpha^3;
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i+1,i+1] := alpha^2*gamma - alpha*beta^2;
            end if;
            if (alpha eq 0) and (gamma ne 0) then
              M[i,i] := gamma^3;
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i+1,i+1] := alpha*gamma^2 - gamma*beta^2;
            end if;
            if (alpha eq 0) and (gamma eq 0) then
              M[i,i+1] := 0;
              M[i+1,i] := 0;
              M[i,i] := 2*beta;
              M[i+1,i+1] := -2*beta;
            end if;
          end if;
        end for;
      end if;
    end if;
    //printf "Diagonalized local splitting is %o.\n",M;

    isaniso := false;
    //printf "Determinant at %o is %o.",p,Determinant(M);

    if Ncols(M) eq 3 then
      d := Determinant(M);
      eps := 1;
      for j in [2..3] do
        for i in [1..j-1] do
          eps := eps*HilbertSymbol(M[i][i], M[j][j],p);
        end for;
      end for;
      if eps ne HilbertSymbol(-1,-d,p) then
        isaniso := true;
      end if;
    end if;

    if Ncols(M) eq 4 then
    if IsPAdicSquare(Determinant(M),p) then
      //printf "The deteriminant is a %o-adic square.\n",p;
      eps := 1;
      for j in [2..4] do
        for i in [1..j-1] do
          eps := eps*HilbertSymbol(M[i][i], M[j][j],p);
        end for;
      end for;
      //printf "eps invariant is %o at %o.\n",eps,p;
      if eps eq (-1)*HilbertSymbol(-1,-1,p) then
        isaniso := true;
      end if;
    end if;
    end if;

    if isaniso then
      Append(~ret,p);
    end if;
  end for;
  return ret;
end function;

/* END ANISOTROPIC PRIMES FUNCTIONS */

/* LOCAL REPRESENTABILITY FUNCTIONS */

// This function coughs up a quadratic non-residue modulo
// an odd prime p.

function NonRes(p)
  done := false;
  q := 1;
  while done eq false do
    q := NextPrime(q);
    if LegendreSymbol(q,p) eq -1 then
      done := true;
    end if;
  end while;
  return q;
end function;

// This function checks that M locally represents
// all necessary integers. Since this function is called
// on an integral matrix, we want M to represent
// all integers congruent to 2 mod 4.

function localrep(M)
  good := true;
  nm := NumberOfRows(M);
  MQ := RMatrixSpace(Q,nm,nm);
  M2 := 2*M;
  M2 := MQ ! M2;
  N := LevelOfQuadForm(M2);
  F := Factorization(2*N);

  // Check whether all appropriate square classes are
  // represented at the primes dividing 4N.
  
  for n in [1..#F] do
    p := F[n][1];
    if p eq 2 then
      //classes := [1, 3, 5, 7];
      classes := [1, 3, 5, 7, 2, 6, 10, 14];
    end if;
    if p gt 2 then
      classes := [1, p];
      Append(~classes,NonRes(p));
      Append(~classes,p*NonRes(p));
    end if;
    localfac := 1;
    for m in [1..#classes] do
      localfac := localfac*LocalDensity(GetLocal(M,p),classes[m],p,[],[]);
    end for;
    if localfac eq 0 then
      good := false;
    end if;
  end for;  
  return good;
end function;

// This function determines which numbers are locally represented by M
// It returns two lists - one of square classes <a,p> that aren't
// represented, and one of square classes <a,p> with the property that
// a*p^(2k) is never represented for any k.

function findlocalrep(M)
  nm := NumberOfRows(M);
  MQ := RMatrixSpace(Q,nm,nm);
  M2 := 2*M;
  M2 := MQ ! M2;
  N := LevelOfQuadForm(M2);
  F := Factorization(4*N);

  badclasses := [];
  foreverclasses := [];
  for n in [1..#F] do
    badclassesp := [];
    foreverclassesp := [];
    p := F[n][1];
    if p eq 2 then
      classes := [1, 3, 5, 7, 2, 6, 10, 14];
    end if;
    if p gt 2 then
      classes := [1, p];
      Append(~classes,NonRes(p));
      Append(~classes,p*NonRes(p));
    end if;
    for m in [1..#classes] do
      locden := LocalDensity(GetLocal(M,p),classes[m],p,[],[]);
      if locden eq 0 then
        done := false;
        cur := classes[m];
        val := 2 + Valuation(cur,p);
        cur := cur*p^2;
        forever := false;
        while done eq false do
          locden := LocalDensity(GetLocal(M,p),cur,p,[],[]);
          if locden gt 0 then
            done := true;
            for mm in [0..Floor((val-2)/2)] do
              Append(~badclassesp,classes[m]*p^(2*mm));
            end for;
          end if;
          val := val + 2;
          cur := cur*p^2;
          if val gt F[n][2]+2 and done eq false then
            done := true;
            forever := true;
            Append(~foreverclassesp,classes[m]);
          end if;
        end while;
      end if;
    end for;
    for m in [1..#badclassesp] do
      Append(~badclasses,<badclassesp[m],p>);
    end for;
    for m in [1..#foreverclassesp] do
      Append(~foreverclasses,<foreverclassesp[m],p>);
    end for;
  end for;
  return badclasses, foreverclasses;
end function;

/* END LOCAL REPRESENTABILITY FUNCTIONS */

/* EISENSTEIN BOUND FUNCTIONS */

/* LOCAL JORDAN SPLITTING FUNCTION */

// This function returns a local Jordan splitting
// for a matrix M over Z_p.

// This function takes a rational number a in Q_p and
// returns an integer that is in the same squareclass as a.

function MakeInt(a,p)
  pval := Valuation(a,p);
  a2 := a*p^(-pval);
  b := 1;  
  if p gt 2 then
    a3 := FiniteField(p) ! a2;
    a4 := Z ! a3;
    if LegendreSymbol(a4,p) eq 1 then
      b := 1;
    else
      b := NonRes(p);
    end if;
  end if;
  if p eq 2 then
    a3 := Integers(8) ! a2;
    a4 := Z ! a3;
    b := a4 mod 8;
  end if;
  ret := b*p^(pval);
  return ret;
end function;

function GetLocal(M,p)
  n := NumberOfRows(M);
  done := false;
  while done eq false do
    // Find least p-divisible entry not already taken care of.
    // If there are none, then done = true
    minval := Valuation(0,p);    
    loc := [];
    found := false;
    for a in [1..n] do
      for b in [1..n] do
        if M[a][b] ne 0 then
            // Check if it is taken care of
            takencareof := false;
            if a eq b then
              S := { M[a][c] : c in ([1..b-1] cat [b+1..n]) };
              S := S join { M[c][b] : c in ([1..a-1] cat [a+1..n]) };
              if S eq {0} or #S eq 0 then
                takencareof := true;
              end if;
              if a lt n then
                if M[a][a+1] ne 0 then
                bb := a+1;
                if p eq 2 then
                  if Valuation(M[a][a],p) eq Valuation(M[bb][bb],p) then
                    if
  Min(Valuation(M[a][a],p),Valuation(M[bb][bb],p)) gt
  Valuation(M[a][bb],p) then
                      S1 := 
                      { M[a][c] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S2 :=
                      { M[c][a] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S3 := 
                      { M[b][c] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S4 :=
                      { M[c][b] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S := S1 join S2 join S3 join S4;
                      if S eq {0} or #S eq 0 then
                        takencareof := true;
                      end if;
                    end if;
                  end if;
                end if;
              end if;
              end if;
              if a gt 1 then
                if M[a-1][a] ne 0 then
                  bb := a-1;
              

                if p eq 2 then
                  if Valuation(M[a][a],p) eq Valuation(M[bb][bb],p) then
                    if
                  Min(Valuation(M[a][a],p),Valuation(M[bb][bb],p)) gt
                  Valuation(M[a][bb],p) then
                      S1 := 
                      { M[a][c] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S2 :=
                      { M[c][a] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S3 := 
                      { M[b][c] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S4 :=
                      { M[c][b] : c in [1..Min(a,bb)-1] cat [Max(a,bb)+1..n] };
                      S := S1 join S2 join S3 join S4;
                      if S eq {0} or #S eq 0 then
                        takencareof := true;
                      end if;
                    end if;
                  end if;
                end if;

                end if;
              end if;                  
            end if;          
            if a ne b then
              if AbsoluteValue(a-b) eq 1 and p eq 2 then
                if Valuation(M[a][a],p) eq Valuation(M[b][b],p) then
                  if Min(Valuation(M[a][a],p),Valuation(M[b][b],p)) gt
              Valuation(M[a][b],p) then
 
                    S1 := 
                    { M[a][c] : c in [1..Min(a,b)-1] cat [Max(a,b)+1..n] };
                    S2 :=
                    { M[c][a] : c in [1..Min(a,b)-1] cat [Max(a,b)+1..n] };
                    S3 := 
                    { M[b][c] : c in [1..Min(a,b)-1] cat [Max(a,b)+1..n] };
                    S4 :=
                    { M[c][b] : c in [1..Min(a,b)-1] cat [Max(a,b)+1..n] };
                    S := S1 join S2 join S3 join S4;
                    if S eq {0} or #S eq 0 then
                      takencareof := true;
                    end if;
                  end if;
                end if;
              end if;  
            end if;
            if takencareof eq false then
              //printf "Found bad spot at %o, %o.\n",a,b;
              //printf "Current matrix = %o.\n",M;
              found := true;
              if Valuation(M[a][b],p) lt minval then
                loc := [a,b];
                minval := Valuation(M[a][b],p);
              end if;
              if Valuation(M[a][b],p) eq minval and a eq b then
                loc := [a,b];
              end if;
            end if;
        end if;
      end for;
    end for;
    if found eq false then
      done := true;
    else
      a := loc[1];
      b := loc[2];
      if a eq b then
        // Change variables to clear diagonal
        for m in [1..n] do
          if m ne a then
            alpha := M[m][m];
            beta := M[m][a];
            gamma := M[a][a];
            c := -beta/gamma;
            // Make change of variables (x_m, x_a) -> (x_m, x_a + cx_m)
            AddColumn(~M,c,a,m);
            AddRow(~M,c,a,m);
          end if;
        end for;
      end if; 
      if a ne b then
        // Permute rows and columns so that |a-b| = 1
        larg := Max({a,b});
        smal := Min({a,b});
        SwapColumns(~M,smal+1,larg);
        SwapRows(~M,smal+1,larg);
        // Clear this 2x2 subblock
        for m in [1..n] do
          if (m ne smal) and (m ne smal+1) then
            alpha := M[smal][smal];
            beta := M[smal][smal+1];
            gamma := M[smal+1][smal+1];
            a := M[smal][m];
            b := M[smal+1][m];
            c := M[m][m];
            // Find d and e so that
            // alpha * d + beta * e = -a
            // beta * d + gamma * e = -b
            d := (b*beta - gamma*a)/(alpha*gamma-beta^2);
            e := (a*beta - alpha*b)/(alpha*gamma-beta^2);
            // Make the substitution (x_smal,x_(smal+1),x_m) ->
            // (x_smal + d*x_m, x_(smal+1) + e*x_m, x_m)
            AddColumn(~M,d,smal,m);
            AddRow(~M,d,smal,m);
            AddColumn(~M,e,smal+1,m);
            AddRow(~M,e,smal+1,m);
          end if; 
        end for;
        alpha := M[smal][smal];
        beta := M[smal][smal+1];
        gamma := M[smal+1][smal+1];
        if p gt 2 then
          //printf "Diagonalizing.\n";
          //printf "Starting with %o x^2 + %o xy + %o y^2.\n",
          //alpha,2*beta,gamma;
          if Valuation(beta,p) lt
                    Min(Valuation(alpha,p),Valuation(gamma,p)) then
            temp := MakeInt(alpha+2*beta+gamma,p);
            M[smal][smal] := temp;
            temp := beta + gamma;
            M[smal+1][smal] := temp;
            M[smal][smal+1] := temp;
            alpha := M[smal][smal];
            beta := M[smal+1][smal];
            gamma := M[smal+1][smal+1];
            // Now, ord_p(alpha) = ord_p(beta)
          end if;
          // Diagonalize
          if Valuation(beta,p) ge Valuation(alpha,p) then
            c := -beta/alpha;
            temp := MakeInt(alpha*c^2 + 2*beta*c + gamma,p);
            M[smal+1][smal+1] := temp;
            M[smal][smal+1] := 0;
            M[smal+1][smal] := 0;
            alpha := M[smal][smal];
            beta := M[smal+1][smal];
            gamma := M[smal+1][smal+1];
            else
            c := -beta/gamma;
            M[smal][smal+1] := 0;
            M[smal+1][smal] := 0;
            temp := MakeInt(a + 2*beta*c + gamma*c^2,p);
            M[smal][smal] := temp;
            alpha := M[smal][smal];
            beta := M[smal+1][smal];
            gamma := M[smal+1][smal+1];
          end if;
          //printf "Finally %o x^2 + %o xy + %o y^2.\n",alpha,2*beta,gamma;
        end if;
        if p eq 2 then
          if Valuation(alpha,p) ne Valuation(gamma,p) then
            // (2*beta)^2 - 4*alpha*gamma = c^2 in Z_2
            // and the form is equivalent to c xy
            c := (2*beta)^2 - 4*alpha*gamma;
            v := Valuation(c,2);
            d := 2^(Floor(v/2));
            M[smal][smal] := 0;
            M[smal][smal+1] := d/2;
            M[smal+1][smal] := d/2;
            M[smal+1][smal+1] := 0;
          end if;
        end if;
      end if;
    end if;
  end while;
  // Clear all denominators that are coprime to p
  d := LCM([ Denominator(M[i][j]) : i in [1..n], j in [1..n] ]);
  // Fortunately, no half-integer entries on diagonal if p eq 2  
  d := d div p^(Valuation(d,p));
  // Multiply M by a square that is a multiple of d.
  M := d*MakeInt(1/d,p)*M;
  ret2 := M;
  return ret2;
end function;

/* COUNT POINTS */

// This functions takes a list L = [c_1,...,c_n] and
// a prime number p and counts the number of good points on the
// projective hypersurface c_1 x_1^2 + c_2 x_2^2 + ...
// + c_n x_n^2 = 0 over F_p. (i.e. there is at least one
// i so that c_i x_i ne 0). This function is
// recursive. We also assume that p ne 2.

forward ProjCount;

function ProjCount(L,p)
  //printf "ProjCount called with L = %o and p = %o.\n",L,p;
  n := #L;
  // Coerce L into Z.
  L2 := [];
  for i in [1..n] do
    F := FiniteField(p);
    temp := F ! L[i];
    temp := Z ! temp;
    Append(~L2,temp);
  end for;
  L := L2;

  if (n eq 0 or n eq 1) then
    return 0;
  end if;
  for i in [1..n] do
    if L[i] mod p eq 0 then
      L2 := Remove(L,i);
      return ProjCount(L2,p);
    end if;
  end for;
  // If we get here, all the c_i are nonzero mod p.
  if n mod 2 eq 1 then
    ret := Floor((p^(n-1) - 1)/(p-1));
    return ret;
  end if;
  prod := 1;
  for i in [1..n] do
    prod := (prod*L[i]) mod p;
  end for;
  if n mod 2 eq 0 then
    ret := Floor((p^(n-1) - 1)/(p-1));
    squar := (-1)^(Floor(n/2))*prod;
    ret := ret + LegendreSymbol(squar,p)*p^(Floor((n-2)/2));
    return ret;
  end if;
end function;

/* LOCAL DENSITY FUNCTIONS */

/* PARSE BLOCK FUNCTION */

// This function takes a square matrix, and index i, a number n
// and a prime p. It determines the minimal p-adic valuation
// of the coefficients of the n-variable quadratic form there.

function blockval(M,i,n,p)
  if n eq 1 then
    return Valuation(M[i][i],p);
  end if;
  ret := 0;
  if n eq 2 then
    if p eq 2 then
      a := Valuation(M[i][i],p);
      b := 1+Valuation(M[i][i+1],p);
      c := Valuation(M[i+1][i+1],p);
      if a le b and a le c then
        ret := a;
      end if;
      if b le a and b le c then
        ret := b;
      end if;
      if c le a and c le b then
        ret := c;
      end if;
    end if;
    if p gt 2 then
      a := Valuation(M[i][i],p);
      b := Valuation(M[i][i+1],p);
      c := Valuation(M[i+1][i+1],p);
      if a le b and a le c then
        ret := a;
      end if;
      if b le a and b le c then
        ret := b;
      end if;
      if c le a and c le b then
        ret := c;
      end if;
    end if;
  end if;
  return ret;
end function;

/* GOOD LOCAL DENSITY FUNCTION */

// This function computes the local good
// density, where we consider X so that one
// of p^(v_j) x_j is not congruent to 0 mod p
// where Q = sum p^(v_j) Q_j is the local
// Jordan splitting. This function
// only counts solutions subject to the
// additional conditions that x_j = 0
// mod p for all j in V1 and x_j <> 0 mod p
// for all j in V2.

function LocalGoodDensity(M,m,p,V1,V2)
  V1S := {};
  for n in [1..#V1] do
    V1S := V1S join {V1[n]};
  end for;
  V2S := {};
  for n in [1..#V2] do
    V2S := V2S join {V2[n]};
  end for;
  if p eq 2 then
    // Just count
    if NumberOfRows(M) eq 3 then
      // Parse the splitting
      sizelist := [];
      v := [];
      if M[1,2] ne 0 then
        sizelist := [2,1];
        Append(~v,blockval(M,1,2,p));
        Append(~v,Valuation(M[3,3],2));
      end if;
      if M[2,3] ne 0 then
        sizelist := [1,2];
        Append(~v,Valuation(M[1,1],2));
        Append(~v,blockval(M,2,2,p));
      end if;
      if M[1,2] eq 0 and M[2,3] eq 0 then
        sizelist := [1,1,1];
        Append(~v,Valuation(M[1,1],2));
        Append(~v,Valuation(M[2,2],2));
        Append(~v,Valuation(M[3,3],2));
      end if;
      L := [];
      count := 0;
      for x in [1..8] do
        for y in [1..8] do
          for z in [1..8] do
            L := [x,y,z];
            a := Z ! M[1,1];
            b := Z ! (2*M[1,2]);
            c := Z ! M[2,2];
            d := Z ! (2*M[2,3]);
            e := Z ! M[3,3];
            A := a*x^2 + b*x*y;
            A := A + c*y^2 + d*y*z + e*z^2;
            if (A mod 8) eq (m mod 8) then
              // check congruence conditions
              v2 := [];
              minv := [];
              count2 := 0;
              for n in [1..#sizelist] do
                v3 := [];
                for mm in [1..sizelist[n]] do
                  count2 := count2 + 1;
                  Append(~v3,L[count2]);
                end for;
                Append(~v2,v3);
              end for;
              for n in [1..#sizelist] do
                for mm in [1..sizelist[n]] do
                  if mm eq 1 then
                    minval := Valuation(v2[n][mm],2);
                  end if;
                  if Valuation(v2[n][mm],2) lt minval then
                    minval := Valuation(v2[n][mm],2);
                  end if;
                end for;
                Append(~minv,minval);
              end for;


              isgood := false;
              check := true;
              for n in [1..#sizelist] do
                if v[n] + minv[n] eq 0 then
                  isgood := true;
                end if;
                if n in V1S and minv[n] eq 0 then
                  check := false;
                end if;
                if n in V2S and minv[n] gt 0 then
                  check := false;
                end if;
              end for;
              if isgood and check then
                count := count + 1;
              end if;
            end if;
          end for;
        end for;
      end for;
    end if;

    if NumberOfRows(M) eq 4 then
      // Parse the splitting
      sizelist := [];
      v := [];
      if M[1,2] ne 0 and M[3,4] ne 0 then
        sizelist := [2,2];
        Append(~v,blockval(M,1,2,p));
        Append(~v,blockval(M,3,2,p));
      end if;
      if M[1,2] ne 0 and M[3,4] eq 0 then
        sizelist := [2,1,1];
        Append(~v,blockval(M,1,2,p));
        Append(~v,Valuation(M[3,3],2));
        Append(~v,Valuation(M[4,4],2));
      end if;
      if M[1,2] eq 0 and M[2,3] ne 0 then
        sizelist := [1,2,1];
        Append(~v,Valuation(M[1,1],2));
        Append(~v,blockval(M,2,2,p));
        Append(~v,Valuation(M[4,4],2));
      end if;
      if M[1,2] eq 0 and M[2,3] eq 0 and M[3,4] ne 0 then
        sizelist := [1,1,2];
        Append(~v,Valuation(M[1,1],2));
        Append(~v,Valuation(M[2,2],2));
        Append(~v,blockval(M,3,2,p));
      end if;
      if M[1,2] eq 0 and M[2,3] eq 0 and M[3,4] eq 0 then
        sizelist := [1,1,1,1];
        Append(~v,Valuation(M[1,1],2));
        Append(~v,Valuation(M[2,2],2));
        Append(~v,Valuation(M[3,3],2));
        Append(~v,Valuation(M[4,4],2));
      end if;
      L := [];
      count := 0;
      for x in [1..8] do
        for y in [1..8] do
          for z in [1..8] do
            for w in [1..8] do
              L := [x,y,z,w];
              a := Z ! M[1,1];
              b := Z ! (2*M[1,2]);
              c := Z ! M[2,2];
              d := Z ! (2*M[2,3]);
              e := Z ! M[3,3];
              f := Z ! (2*M[3,4]);
              g := Z ! M[4,4];
              A := a*x^2 + b*x*y + c*y^2;
              A := A + d*y*z + e*z^2 + f*z*w;
              A := A + g*w^2;
              if (A mod 8) eq (m mod 8) then
                // check congruence conditions
                v2 := [];
                minv := [];
                count2 := 0;
                for n in [1..#sizelist] do
                  v3 := [];
                  for mm in [1..sizelist[n]] do
                    count2 := count2 + 1;
                    Append(~v3,L[count2]);
                  end for;
                  Append(~v2,v3);
                end for;
                for n in [1..#sizelist] do
                  for mm in [1..sizelist[n]] do
                    if mm eq 1 then
                      minval := Valuation(v2[n][mm],2);
                    end if;
                    if Valuation(v2[n][mm],2) lt minval then
                      minval := Valuation(v2[n][mm],2);
                    end if;
                  end for;
                  Append(~minv,minval);
                end for;


                isgood := false;
                check := true;
                for n in [1..#sizelist] do
                  if v[n] + minv[n] eq 0 then
                    isgood := true;
                  end if;
                  if n in V1S and minv[n] eq 0 then
                    check := false;
                  end if;
                  if n in V2S and minv[n] gt 0 then
                    check := false;
                  end if;
                end for;
                if isgood and check then
                  count := count + 1;
                end if;
              end if;
            end for;
          end for;
        end for;
      end for;
    end if;
    ret := count/(8^(NumberOfRows(M)-1));
    return ret;
  end if;
  if p gt 2 then
    // count solutions mod p, but be clever
    n := NumberOfRows(M);
    // Measure the density
    retfac := 1/p^(n-1);
    Mnewlist := [];
    for mm in [1..n] do
      throwout := false;
      if Valuation(M[mm][mm],p) gt 0 then
        throwout := true;
      end if;
      if mm in V1S then
        throwout := true;
      end if;
      if throwout eq true then
        if mm in V2S then
          retfac := retfac*(p-1);
        end if;
        if not (mm in V1S) then
          retfac := retfac*p;
        end if;
        Append(~Mnewlist,0);
      end if;
      if throwout eq false then
        Append(~Mnewlist,M[mm][mm]);
      end if;
    end for;
    if #Mnewlist eq 0 then
      return 0;
    end if;
    // Do the counting, and don't forget
    // about making x_n nonzero if n in V2S.
    if m mod p eq 0 then
      retfac := retfac*(p-1);
    end if;
    if m mod p ne 0 then
      Append(~Mnewlist,-m);
      V2S := V2S join {#Mnewlist};
    end if;
    PS := Subsets(V2S);
    PS := SetToIndexedSet(PS);
    ret := 0;
    for n in [1..#PS] do
      sb := PS[n];
      Mtemplist := [];
      // Make x_n zero if n is in sb.
      for n in [1..#Mnewlist] do
        if not (n in sb) then
          Append(~Mtemplist,Mnewlist[n]);
        end if;
      end for;
      counttemp := ProjCount(Mtemplist,p);
      ret := ret + ((-1)^(#sb))*counttemp;
    end for;
    ret := ret*retfac;
    return ret;
  end if;
end function;

/* ZERO DENSITY FUNCTION */

// This function computes the zero density,
// which is related to the number of x
// so that Q(x) = m (mod p^k) with x = 0 mod p.

function LocalZeroDensity(M,m,p,V1,V2)
  // When do we return zero?
  if Valuation(m,p) lt 2 or #V2 gt 0 then
    return 0;
  end if;
  mnew := Floor(m/p^2);
  n := NumberOfRows(M);
  denfac := 1/(p^(n-2));
  // Process congruence conditions before recursion
  V1 := [];
  V2 := [];
  return denfac*LocalDensity(M,mnew,p,V1,V2);
end function;

/* BAD DENSITY FUNCTION */

// This function computes the bad density,
// where p^(v_j) x_j = 0 mod p for all j.
// We assume that M is primitive.

function LocalBadDensity(M,m,p,V1,V2)
  //printf "Bad Density called with M = %o, m = %o.\n",M,m;
  V1S := {};
  for n in [1..#V1] do
    V1S := V1S join {V1[n]};
  end for;
  V2S := {};
  for n in [1..#V2] do
    V2S := V2S join {V2[n]};
  end for;

  // Parse the splitting
  if NumberOfRows(M) eq 3 then
    sizelist := [];
    v := [];
    if M[1,2] ne 0 then
      sizelist := [2,1];
      Append(~v,blockval(M,1,2,p));
      Append(~v,Valuation(M[3,3],p));
    end if;
    if M[2,3] ne 0 then
      sizelist := [1,2];
      Append(~v,Valuation(M[1,1],p));
      Append(~v,blockval(M,2,2,p));
    end if;
    if M[1,2] eq 0 and M[2,3] eq 0 then
      sizelist := [1,1,1];
      Append(~v,Valuation(M[1,1],p));
      Append(~v,Valuation(M[2,2],p));
      Append(~v,Valuation(M[3,3],p));
    end if;
  end if;

    if NumberOfRows(M) eq 4 then
      // Parse the splitting
      sizelist := [];
      v := [];
      if M[1,2] ne 0 and M[3,4] ne 0 then
        sizelist := [2,2];
        Append(~v,blockval(M,1,2,p));
        Append(~v,blockval(M,3,2,p));
      end if;
      if M[1,2] ne 0 and M[3,4] eq 0 then
        sizelist := [2,1,1];
        Append(~v,blockval(M,1,2,p));
        Append(~v,Valuation(M[3,3],p));
        Append(~v,Valuation(M[4,4],p));
      end if;
      if M[1,2] eq 0 and M[2,3] ne 0 then
        sizelist := [1,2,1];
        Append(~v,Valuation(M[1,1],p));
        Append(~v,blockval(M,2,2,p));
        Append(~v,Valuation(M[4,4],p));
      end if;
      if M[1,2] eq 0 and M[2,3] eq 0 and M[3,4] ne 0 then
        sizelist := [1,1,2];
        Append(~v,Valuation(M[1,1],p));
        Append(~v,Valuation(M[2,2],p));
        Append(~v,blockval(M,3,2,p));
      end if;
      if M[1,2] eq 0 and M[2,3] eq 0 and M[3,4] eq 0 then
        sizelist := [1,1,1,1];
        Append(~v,Valuation(M[1,1],p));
        Append(~v,Valuation(M[2,2],p));
        Append(~v,Valuation(M[3,3],p));
        Append(~v,Valuation(M[4,4],p));
      end if;
    end if;

  maxj := #sizelist;
  S0 := {};
  S1 := {};
  S2 := {};
  for n in [1..maxj] do
    if v[n] eq 0 then
      S0 := S0 join {n};
    end if;
    if v[n] eq 1 then
      S1 := S1 join {n};
    end if;
    if v[n] gt 1 then
      S2 := S2 join {n};
    end if;
  end for;

  // Are there any bad solutions?
  // There are no bad solutions if either
  // x must be congruent to 0
  if #V1S eq maxj or (m mod p ne 0) then
    return 0;
  end if;
  // or some n in S0 requires x_n not congruent to zero
  if #(V2S meet S0) gt 0 then
    return 0;
  end if;

  // Parse type I and type II

  // Type I

  retbad1 := 0;
  // We need S1 not empty, and the congruence conditions
  // allowing x_j ne 0 for some j in S1.
  if #S1 gt 0 and #(V1S meet S1) ne #S1 then
    mnew := Floor(m/p);
    Mnew := M;

    for n in S0 do
      // Increase valuation by 1
      start := 1;
      for m in [1..n-1] do
        start := start + sizelist[m];
      end for;
      last := start + sizelist[n] - 1;
      for i in [start..last] do
        for j in [start..last] do
          Mnew[i,j] := Mnew[i,j]*p;
        end for;
      end for;
    end for;

    for n in (S1 join S2) do
      // Decrease valuation by 1
      start := 1;
      for m in [1..n-1] do
        start := start + sizelist[m];
      end for;
      last := start + sizelist[n] - 1;
      for i in [start..last] do
        for j in [start..last] do
          Mnew[i,j] := Mnew[i,j]/p;
        end for;
      end for;
    end for;
    n := NumberOfRows(M);
    retfac := 1/p^(n-1);
    for m in [1..maxj] do
      if m in (S1 join S2) then
        retfac := retfac*p^(sizelist[m]);
      end if;
    end for;
    V1new := [];
    V2new := [];
    for m in [1..n] do
      if (m in (S1 join S2)) and m in V1S then
        Append(~V1new,m);
      end if;
      if (m in (S1 join S2)) and m in V2S then
        Append(~V2new,m);
      end if;
    end for;
    retbad1 := retfac*LocalGoodDensity(Mnew,mnew,p,V1new,V2new);
  else
    retbad1 := 0;
  end if;

  // Type II
  retbad2 := 0;
  // We need the congruence conditions
  // allowing x_j = 0 for all j in S1, S_2 to be nonempty but
  // and p^2 | m.
  if #(V2S meet S1) eq 0 and #S2 gt 0 and Valuation(m,p) gt 1 then
    mnew := Floor(m/p^2);
    Mnew := M;

    for n in S2 do
      // Decrease valuation by 2
      start := 1;
      for m in [1..n-1] do
        start := start + sizelist[m];
      end for;
      last := start + sizelist[n] - 1;
      for i in [start..last] do
        for j in [start..last] do
          Mnew[i,j] := Mnew[i,j]/(p^2);
        end for;
      end for;
    end for;

    retfac := p^2;
    for m in [1..maxj] do
      if m in (S0 join S1) then
        retfac := retfac*(1/p^(sizelist[m]));
      end if;
    end for;
    V1new1 := [ i : i in V1 | (i in S2)];
    V2new1 := [ i : i in V2 | (i in S2)];
    V1new2 := [ i : i in S2 ];
    V2new2 := V2new1;
    retbad2 := retfac*(LocalDensity(Mnew,mnew,p,V1new1,V2new1)-
    LocalDensity(Mnew,mnew,p,V1new2,V2new2));
  else
    retbad2 := 0;
  end if;

  //printf "Returning from Bad. Type I = %o, Type II =
  //%o.\n",retbad1,retbad2;
  //printf "retfac = %o.\n",retfac;
  return retbad1 + retbad2;
end function;

// This function computes the local density
// # \{ X \in \Z/p^k\Z : f(X) = m (mod p^k)}
// divided by p^(n-1)(k-1). This function
// should work for a quadratic form of
// dimension 3 or 4. We assume that M
// is a symmetric matrix with integral entries and
// an even diagonal. If M is a the matrix
// of an integral quadratic form (so the off-diagonal entries
// may be non-integral) the appropriate call is LocalDensity(M,m,p,V1,V2);
// The matrix M should be a local Jordan splitting.

/* LOCAL DENSITY FUNCTION */

function LocalDensity(M,m,p,V1,V2)
  if p lt 5 then
    //printf "LocalDensity called with parameters %o %o %o %o %o.\n",M,m,p,V1,V2;
  end if;

  LGD := LocalGoodDensity(M,m,p,V1,V2);
  LZD := LocalZeroDensity(M,m,p,V1,V2);
  LBD := LocalBadDensity(M,m,p,V1,V2);
  if p lt 5 then
    //printf "LGD = %o, LZD = %o, LBD = %o.\n",LGD,LZD,LBD;
  end if;
  ret := LGD + LZD + LBD;
  return ret;
end function;

// This function computes the local density at infinity
// of the quadratic form. It is only a function of
// the discriminant and conductor.

function InfinitePlace(M,m)
  n := NumberOfRows(M);
  D := Determinant(M)/(2^n);
  if n eq 3 then
    omegan := (4/3)*Pi(R);    
  end if;
  if n eq 4 then
    omegan := (1/2)*Pi(R)^2;
  end if;
  ret := ((n*omegan)/(2*D^(1/2)))*m^((n-2)/2);
  return ret;
end function;

// This function computes the infinite place part of the
// Eisenstein bound

/* INFINITE PLACE BOUND FUNCTION */

// Return value is 2*omega_4 * D^(-1/2) * L(2,chi)^(-1)
// here omega_4 is the volume of the sphere of radius
  // 1 in four dimensions = (Pi^2/2);

function InfiniteBound(D,N)
  D := Floor(D);

  // Evaluate the L-value
  // Compute the Bernoulli number
  if IsSquare(D) then
    chi := KroneckerCharacter(1,RationalField());
  else
    chi := KroneckerCharacter(FundamentalDiscriminant(D),RationalField());
  end if;
  q := Conductor(chi);
  B := 0;
  for i in [1..q] do
    B := B + Evaluate(chi,i)*(6*i^2 + q^2 - 6*i*q)/(12*q);
  end for;
  //printf "Bernoulli number is %o.\n",B;

  // Since L(2,chi) = ((pi^2)/(q^(3/2)))*B_2,chi, the return value
  // is q^(3/2) D^(-1/2) B_2,chi^(-1)
  issqr, root := IsSquare(q^3/D);
  //printf "Sqrt(q^3/D) is %o.\n",root;
  if issqr then
    ret := (2*root)/(B);
  else
    PrintFile(LOGFILE,"ERROR: Wrong square class for discriminant.");
    ret := 0;
    quit;
  end if;
  return ret;
end function;

/* THEORETIC EISENSTEIN BOUND FUNCTION */

// Compute the Eisenstein series lower bound
// This is analogous to Hanke's
// _new_C4_rational & _C4_squareclass_constants
// The function takes the matrix and the anisotropic primes
// This function is passed the (not necessarily integral) matrix

function TheoEisenstein(M,A)
  D := Z ! Determinant(2*M);
  N := LevelOfQuadForm(2*M);
  ret := InfiniteBound(D,N);
  F := Factorization(N);
  if IsSquare(D) then
    chi := KroneckerCharacter(1,RationalField());
  else
    chi := KroneckerCharacter(FundamentalDiscriminant(D),RationalField());
  end if; 
  for n in [1..#F] do
    p := F[n][1];
    ret := ret*(1/(1 - Evaluate(chi,p)/p^2));
    aniso := false;
    for m in [1..#A] do
      if p eq A[m] then
        aniso := true;
      end if;
    end for;
    // for each prime p dividing the conductor, 
    // compute the lower bound for each
    // square class in Z_p. Since we are
    // excluding even numbers, there are 4 square
    // classes mod 2, and 4 square classes mod every
    // odd prime
    if p eq 2 then
      classes := [1, 3, 5, 7, 2, 6, 10, 14];
      // If we wanted all integers, we would have
      // classes := [1, 3, 5, 7, 2, 6, 10, 14];
    end if;
    if p gt 2 then
      classes := [1, p];
      Append(~classes,NonRes(p));
      Append(~classes,p*NonRes(p));
    end if;
    Stable := Floor((Valuation(N,p)+1)/2);
    mins := [];
    if aniso eq false then
      for m in [1..#classes] do
        DV := [];
        // Find min for each class
        for j in [0..Stable+2] do
          Append(~DV,LocalDensity(GetLocal(M,p),classes[m]*p^(2*j),p,[],[]));
        end for;
        Cp := ((DV[Stable+3]/DV[Stable+2])*p^2 - 1)/(p^2-1);
        Cp1 := Min(Cp,1);
        DV[Stable+3] := DV[Stable+2]*Cp1;
        // Find min for this squareclass
        tmin := 0;
        for m in [1..Stable+3] do
          if DV[m] gt 0 and (tmin eq 0 or DV[m] lt tmin) then
            tmin := DV[m];
          end if;
        end for;
        Append(~mins,tmin);
      end for;
    end if;
    if aniso eq true then
      for m in [1..#classes] do
        DV := [];
        t := classes[m];
        // Find min for each class
        for j in [0..Stable+2] do
          Append(~DV,LocalDensity(GetLocal(M,p),t*p^(2*j),p,[],[])*
          (p^(Valuation(t,p)+2*j)));
        end for;
        tmin := 0;
        for m in [1..Stable+3] do
          if DV[m] gt 0 and (tmin eq 0 or DV[m] lt tmin) then
            tmin := DV[m];
          end if;
        end for;
        Append(~mins,tmin);
      end for;
    end if;
    //printf "For p = %o, the local minima are %o.\n",p,mins;
    // Take min of nonzero entries in DV to get min for p
    minp := 0;
    for m in [1..#mins] do
      if mins[m] gt 0 and (minp eq 0 or mins[m] lt minp) then
        minp := mins[m];
      end if;
    end for;
    ret := ret*minp;
  end for;
  return ret;
end function;

/* APPROXIMATE EISENSTEIN BOUND FUNCTIONS */

// This function takes the matrix M and
// the list of anisotropic primes A
// and computes the actual Eisenstein lower bound.
// We default to use 500 terms. Also computes the
// numerical cusp form bound.

function ApproxEisenstein(M,A,T,Eis)
  Anisos := Seqset(A);
  prec := 5000;
  Cusp := T - Eis;
  N := LevelOfQuadForm(2*M);
  D := Determinant(2*M);
  if IsSquare(D) then
    eps := 1; 
  else
    eps := FundamentalDiscriminant(Integers() ! D);
  end if;
  chi := DirichletGroup(N)!KroneckerCharacter(eps);
  //printf "Eisenstein series is %o.\n",T+BigO(q^100);
  //printf "Cusp form is %o.\n",Cusp+BigO(q^100);
  min := -1;
  max := 0;
  excep := [];
  for m in [1..prec] do
    F := Factorization(m);
    miso := m;
    fac := 1;
    for k in [1..#F] do
      if F[k][1] in Anisos then
        miso := miso/(F[k][1]^F[k][2]);
      end if;
      if Gcd(F[k][1],N) eq 1 and chi(F[k][1]) eq -1 then
        fac := fac*((F[k][1]-1)/(F[k][1]+1));
      end if;
    end for;
    mbound := Coefficient(Eis,m)/(fac*miso);
    if min eq -1 or mbound lt min then
      //printf "Coefficient %o has bound value %o.\n",m2,mbound;
      min := mbound;
    end if;
    if Coefficient(T,m) eq 0 then
      Append(~excep,m);
    end if;
    // Look at all cusp form coefficients.
    cuspterm := R ! Coefficient(Cusp,m);
    cuspterm := Abs(cuspterm);
    cuspterm := cuspterm/(NumberOfDivisors(m)*Sqrt(m));
    if cuspterm gt max then
      max := cuspterm;
    end if;
  end for;
  return min, max, excep;
end function;

/* END EISENSTEIN BOUND FUNCTIONS */

/* SPLIT LOCAL COVER FUNCTIONS */

// This routine finds a split local cover for M, i.e.
// a form dx^2 + Q(y,z,w) that is the quadratic form
// of a sublattice of the lattice corresponding to M.
// Further, dx^2 + Q(y,z,w) has the property that it locally represents
// all integers represented by M, and d is minimal with
// this property. It returns d and the gram matrix of the ternary
// sublattice.

function SplitLocal(M)
  done := false;
  MZ := RMatrixSpace(Z,4,4);
  MQ := RMatrixSpace(Q,4,4);
  MQ3 := RMatrixSpace(Q,3,3);
  M2 := 2*M;
  M2 := MZ ! M2;
  L := LatticeWithGram(M2);
  d := 2;
  while done eq false do
    //printf "trying d = %o.\n",Floor(d/2);
    // Find all vectors of norm d
    V := ShortVectors(L,d,d);
    for n in [1..#V] do
      v := V[n][1];
      // Construct the orthogonal complement of v
      c := [];
      for m in [1..4] do
        term := 0;
        term := M2[m][1]*v[1] + M2[m][2]*v[2] + M2[m][3]*v[3] + M2[m][4]*v[4];
        Append(~c,term);
      end for;
      Mod1 := RSpace(Z,4);
      Mod2 := RSpace(Z,1);
      H := Hom(Mod1,Mod2);
      Mapp := H ! [c[1], c[2], c[3], c[4]];
      SubL := Basis(Kernel(Mapp));
      v1 := L ! SubL[1];
      v2 := L ! SubL[2];
      v3 := L ! SubL[3];
      L2 := sub<L | v, v1, v2, v3>;
      M3 := GramMatrix(L2);
      M3 := MQ ! M3;
      M3 := M3/2;
      //printf "Testing %o for local representability.\n",M3;
      if localrep(M3) then
        done := true;
        retd := Floor(d/2);
        L3 := sub<L | v1, v2, v3>;
        M4 := GramMatrix(L3);
        retM := MQ3 ! M4;
      end if;      
    end for; 
    if done eq false then
      d := d + 2;
    end if;  
  end while;
  return retd, retM;
end function;

// U(d) operator

function U(f,d)
  qq := Parent(f).1;
  start := Valuation(f);
  en := AbsolutePrecision(f)-1;
  ret := 0;  
  for n in [start..en] do
    if (n mod d eq 0) then
      ret := ret + Coefficient(f,n)*qq^(Floor(n/d));
    end if;
  end for;
  ret := ret + BigO(qq^(Ceiling(AbsolutePrecision(f)/d)));
  return ret;
end function;

// V(d) operator

function V(f,d)
  qq := Parent(f).1;
  start := Valuation(f);
  en := AbsolutePrecision(f)-1;
  ret := 0;  
  for n in [start..en] do
    ret := ret + Coefficient(f,n)*qq^(n*d);
  end for;
  ret := ret + BigO(qq^(AbsolutePrecision(f)*d));
  return ret;
end function;

/* Main program */

function runPrelim()
   PrintFile(LOGFILE,Sprintf("Summary for Form #%o.",mmm));
   PrintFile(DATAFILE,Sprintf("mmm := %o;", mmm));
   
   PrintFile(LOGFILE,Sprintf("Form has matrix %o.",M));
   PrintFile(DATAFILE,Sprintf("M := %o;", M));
   
   tim := Cputime();
   
   // Determine the level
   
   NNNN := LevelOfQuadForm(2*M);
   PrintFile(LOGFILE,
   Sprintf("This form has level %o.",NNNN));
   PrintFile(DATAFILE,Sprintf("NNNN :=%o;",NNNN));
   
   // Determine the character
   
   D := Determinant(2*M);
   if IsSquare(D) then
     eps := 1; 
   else
     eps := FundamentalDiscriminant(Integers() ! D);
   end if;
   
   PrintFile(LOGFILE,Sprintf("It has character %o.",eps));
   PrintFile(DATAFILE,Sprintf("chi := DirichletGroup(%o)!KroneckerCharacter(%o);",NNNN,eps));
   
   // Compute the anisotropic primes
   
   A := aniso(2*M);
   
   PrintFile(LOGFILE,Sprintf("The list of anisotropic primes is
   %o.",A));
   PrintFile(DATAFILE,Sprintf("aniso := %o;", A));
   
   // Check that the numbers we care about are locally represented
   // I question whether this is necessary
   
   localcheck := localrep(M);
   
   PrintFile(LOGFILE,Sprintf("Are all integers locally represented? %o.",localcheck));
   
   if localcheck eq false then
     PrintFile(LOGFILE,"ERROR: This form doesn't locally represent all integers!");
   end if;
   
   // Pre-compute theta series and Eisenstein series
   
   R<q> := PowerSeriesRing(RationalField());
   chi := DirichletGroup(NNNN)!KroneckerCharacter(eps);
   C := CuspForms(chi);
   coeff_bound := Max(5000,20*Dimension(C));
   L := LatticeWithGram(2*M);
   D := Integers()!Determinant(2*M);
   PrintFile(LOGFILE,"Pre-computing theta series and Eisenstein series.");
   PrintFile(LOGFILE,Sprintf("Cusp dimension is %o. Precision is %o.\n",Dimension(C),coeff_bound));
   T := U(R!ThetaSeries(L,2*coeff_bound),2);
   
   //printf "Using local densities to compute Eisenstein series...\n";
   
   qq := Conductor(chi);
   
   //printf "Form %o, level %o and Nebentypus %o.\n",mmm,N,qq;
   B := 0;
   for i in [1..qq] do
     B := B + Evaluate(KroneckerCharacter(eps),i)*(6*i^2 + qq^2 - 6*i*qq)/(12*qq);
   end for;
   // printf "Bernoulli number is %o.\n",B;
   // L(2,chi) = ((pi^2)/(q^(3/2)))*B_2,chi
   chk, sqrt := IsSquare(D/qq);
   // Modify for primes dividing D/q
   F := Factorization(2*D);
   primelist := [ F[i][1] : i in [1..#F] | GCD(qq,F[i][1]) eq 1 ];
   fac := (2/sqrt)*(qq/B);
   if #primelist ge 1 then
     fac := fac*(&*[ (1-Evaluate(KroneckerCharacter(eps),p)/p^2)^(-1) : p in primelist]);
   end if;
   
   Eis := R!1 + BigO(q^(coeff_bound+1));
   F := Factorization(2*D);
   
   //printf "Pre-computing local densities...";
   localden := [];
   for n in [1..#F] do
     p := F[n][1];
     localdenlist := [];
     if p eq 2 then
       sqrclasslist := [1,3,5,7];
     else
       sqrclasslist := [1,NonRes(p)];
     end if;  
     localsplit := GetLocal(M,p);
     maxpow := Floor(Log(coeff_bound)/Log(p));
     for mm in [0..maxpow] do
       localdenvec := [];
       for i in [1..#sqrclasslist] do
         num := sqrclasslist[i]*p^mm;
         Append(~localdenvec,LocalDensity(localsplit,num,p,[],[]));
       end for;
       Append(~localdenlist,localdenvec);
     end for;
     Append(~localden,localdenlist);
   end for;
   //printf "Done!\n";
   
   localsplit := [ GetLocal(M,F[r][1]) : r in [1..#F]];
   for m in [1..coeff_bound] do
     eiscoeff := fac*&+[ Evaluate(chi,d)*(m/d) : d in Divisors(m) | GCD(d,2*D) eq 1
    ];
     for r in [1..#F] do
       val := Valuation(m,F[r][1]);
       if F[r][1] eq 2 then
         numonlist := Floor(((Floor(m/F[r][1]^(val)) mod 8)+1)/2);
       else
         numonlist := Floor((3/2)-(1/2)*LegendreSymbol(Floor(m/F[r][1]^(val)),F[r][
   1]));
       end if;
       eiscoeff := eiscoeff*localden[r][val+1][numonlist];
     end for;
     Eis := Eis+eiscoeff*q^m;  
   end for;
   
   // Check to see if a regular ternary sublattice will work
   
   PrintFile(LOGFILE,"Starting cusp constant computation.");
   
   // Compute the cuspidal constant  
   
   CuspC := compute_cusp_constant(2*M,T,Eis,coeff_bound);
   PrintFile(LOGFILE,
   Sprintf("The overall cuspidal constant is %o.",RealField(10)!CuspC));
   maxmem := GetMaximumMemoryUsage();
   PrintFile(LOGFILE,Sprintf("Memory used was %o Mb.",RealField(5)!(maxmem/2^20)));
   
   // Compute the theoretical Eisenstein lower bound
   
   Eislower := TheoEisenstein(M,A);
   
   PrintFile(LOGFILE,Sprintf("The Eisenstein lower bound is %o =
   %o.",Eislower,RealField(7)!Eislower));
   
   // Compute the ratio cuspidal/Eisenstein
   // Add some wiggle room for round-off error
   F4bound := RealField(10)!(1.01*CuspC/Eislower);
   
   PrintFile(LOGFILE,Sprintf("The F4 upper bound is %o.",F4bound));
   PrintFile(DATAFILE,Sprintf("F4bound := %o;", F4bound));
   
   // Check the numerical Eisenstein lower bound
   
   Eismin, Cuspmax, Excep := ApproxEisenstein(M,A,T,Eis);
   
   PrintFile(LOGFILE,
   Sprintf("The numerical Eisenstein lower bound is %o = %o.",
   Eismin,RealField(7)!Eismin));
   
   PrintFile(LOGFILE,
   Sprintf("The numerical cusp form bound is %o.",
   RealField(7)!Cuspmax));
   
   if CuspC lt Cuspmax then
     PrintFile(LOGFILE,"ERROR: Numerical cusp constant greater than theoretical!");end if;
   
   if Eislower gt Eismin then
     PrintFile(LOGFILE,"ERROR: Numerical Eisenstein lower bound less than
     theoretical!");
   end if;
   
   PrintFile(LOGFILE,"The form represents all numbers less than");
   PrintFile(LOGFILE,Sprintf("or equal to 5000 except the following: %o",Excep));
   
   // Compute an appropriate local cover
     
   d, S := SplitLocal(M);
   
   PrintFile(LOGFILE,
   Sprintf("Split local cover of the form [d] + L with d = %o.",d));
   PrintFile(LOGFILE,Sprintf("L = %o.",S));
   
   PrintFile(DATAFILE,Sprintf("d := %o;", d));
   PrintFile(DATAFILE,Sprintf("S := %o;", S));
   
   tim2 := Cputime(tim);
   PrintFile(LOGFILE,
   Sprintf("Preprocessing complete. Time needed is %o sec.",tim2));

   // Whew, that's a lot of return values =)
   return M, d, S, F4bound, NNNN, chi, A;
end function;
