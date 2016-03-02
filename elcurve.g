## This is entered by hand from the print out I found in "Rational Points on Elliptic Curves"
## comments added while entering it this time are marked w/ '##'
##
## I have no idea how up to date this printout is, but I did write in it
## that it was working.
##
## Status: entered all, proofread first 2 pages. Formatted using Gap mode.
## Better double check thewhole thing. Still lots of syntax errors on Read.
## Now (Sat, Jan 02, 2016  6:25:35 PM) proofread pages 1-4 ex. 2. Corrected
## several errors big enough to explain failures. Finally proofread page 2 again, found one error.
## But there must be more: after I removed apparently extra local decls for x2, I ran into x3 as
## "unbound global variable" l73. Fixed. Now error is looking for 'end' l125.
## Now found several missing ';' and one extra 'fi;'!
##
## Now runs, but prints no output. Was I supposed to call it explicitly myself after loading? But
## this fails too.
##
## WORKS! On one test case, that is.
##
#Naive Elliptic Curve Algorithm for factoring Rational Integers
#
#F EFactorsInt(<n>).....prime factors of an integer
#
# Also local functions:
# [ (x1+x2, y1+y2), gcd ] = AddCurves( n, x1, y1, x2, y2)
# and
# [ (2x1,2y1, gcd ] = DoublePoint(x1, y1)
# and
# [ k*(x1,y1), gcd] = ComputekP(n, x1, y1, x2, y2)
#
# Step 1 Check that gcd(n,y) = 1 and that n != m^r for r > 1
#
# Step 2 Choose 'random' r, x1, y1 from 1 to n
#
# Step 3 Compute remaining coefficient c, choose point on C 
#
# Step 4 Compute gcd for termination conditions
#
# Step 5 Compute 'factor base' k
#
# Step 6 Compute k-th multiple of P

StartTime := Runtime();
EndTime := 0;

# Globals here:
dbug:=0;
pow2:=1;
QP:=[0,0,1];   # just to get rid of "undefined global" msg!
powPs:=[];     # powPs[i>=1] will b [x, y, gcd] = 2^i*P

# Very miscellaneous globals: declarations added here just to get rid of msgs!
yt := 0;      # these initial values are not used
yt1 := 0;
yt2 := 0;
lhs := 0;

# locals:
# pows2[i] is 2^i
# binexp is 'binary expansion' ie. list of powers of 2 actually used.
# binexp[i] is power of 2 of ith non-zero power in expansion from left to right

EFactorsInt := function (n)
    local factors, b, c, x1, y1, i,j, k, K, g, il, Q, d, p, quot, binexp, pow2s, ComputekP;
    #g = gcd, il = integer list, d = discriminant # handwritten: x2, y2 appears unneeded.
    ComputekP := function (n, x1, y1, x2, y2)
        local Q, QT, QT1, DoublePoint, AddCurves, QTot, l;
        # handwritten: misnomer: should be 'AddPoints'
        # handwritten: add two points (x1,y1), (x2,y2) on current curve
        AddCurves := function(x1, y1, x2, y2)
            local g, x3, Q3, lambda;
            DoublePoint := function(x1, y1)
                g := GcdInt(y1,n);
                if g = 1 then
                    # derived from Koblitz, not from Sil & Tate # (handwritten): listed in refs in RSANTheory.html?
                    # which gave a wrong formula
                    lambda := QuotientMod(3*x1^2 + b, 2*y1, n);
                    x3 := (lambda^2 mod n - 2*x1) mod n;
                    yt := (-lambda*x3-(y1-lambda*x1)) mod n;
                    lhs := (PowerMod(x3, 3, n) + b*x3 mod n + c) mod n;
                    if dbug<>0 then
                        if lhs <> PowerMod(yt, 2, n) then
                            Print("\nPoint (x,y) = (", x3, ", ", yt, ") not on curve!");
                            Error("nFm Double: Waiting...");
                        fi;
                    fi;

                    Q3 := [x3, yt, g];
                elif g<n then
                    Q3 := [0,0, g];
                else
                    if dbug <> 0 then
                        Print("Bad News fm Double: gcd=n");
                    fi;
                    Q3:= [0,0,n];
                fi;
                return Q3;
            end; # end of DoublePoint

            # Here is where AddCurves actually starts executing.

            # Check for doubling first
            if x1=x2 and y1=y2 then
                Q3 := DoublePoint(x1, y1);
                return Q3;
            fi;

            # First do GCD, check return conditions
            g := GcdInt(x2-x1, n);
            if g = 1 then # these if clauses are the decision portion of Sil&Tate's Step 7
                lambda := QuotientMod(y2-y1, x2-x1, n);
                x3 := (PowerMod(lambda, 2, n) - (x1+x2) mod n) mod n;
                yt1 := -lambda*x3 mod n;
                yt2 := (y1-(lambda*x1 mod n) ) mod n;
                yt  := (yt1-yt2) mod n;
                Q3 := [x3, yt, g];

                # Now that I have Q3, for debug,
                # I will verify that it is on the curve
                lhs := (PowerMod(x3, 3, n) + b*x3 mod n + c) mod n;
                # (handwritten:) Why is this still being executed? (I think I know now: because dbug not referenced)
                if lhs <> PowerMod(yt, 2, n) then
                    Print("\nPoint (x,y) = (", x3, ", ", yt, ") not on curve!");
                    Error("Waiting...");
                fi;
                return Q3;
            elif g<n then
                Q3 := [ 0,0, g];
                return Q3;
            else
                Print("Bad News: gcd=n");
                Q3 := [ 0,0, n];
                return Q3;
            fi;
        end; #end of AddCurves(...) ## or is it?

        # Now start computing kP by doubling
        QP := [x1, y1, 0]; # use 0 fr don't care, since AddCurves will set this
        i := 0;
        pow2 := 1;
        powPs := [];              # for now, we will rebuild this list each time
        pow2s := [];
        while pow2 < k/2 do
            QP := AddCurves(QP[1], QP[2], QP[1], QP[2]);
            if QP[3] <> 1  then
                return QP;                # ret. to caller check termination cndx
            fi;
            i := i+1;
            pow2 := pow2 * 2;
            Add(pow2s, pow2);
            Add(powPs, QP);
        od;
        # Now the above works (sort of), but I am compensating for 1-based
        # arrays by omitting 2^0=1 in pows2!
        # thus at this point I have computed all the necessary powers of two
        # and 2^i*P up to highest power needed.

        # Now build binary expansion of k
        # This loop works much better now! It correct computes digits of k=12252240
        # (the example from Sil & Tate)

        quot := k;
        binexp :=[]; # will be table of powers of 2 needed
        repeat       ## this starts the loop...
            if pow2s[i] <= quot then
                quot := quot - pow2s[i];
                Add(binexp, i);
            fi;
            i:=i-1;
        until quot <= 1; ## this finishes the repeat... until loop.

        # Thus at this point we have all the powers of two which need to be added
        #  up to get kP in Binexp.
        # Now use binexp to determine which powers of P to add
        l := Length(binexp);
        QT1 := powPs[binexp[l]];
        QTot := [QT1[1], QT1[2], 1]; ## yes, these really are all the digit '1' not the letter 'l'
        QT := QTot;                  # QT Q Temporary
        i := 2;
        while i <= l do
            QT := powPs[binexp[l-i+1]];
            QT1 := AddCurves(QTot[1], QTot[2], QT[1], QT[2]);
            if QT1[3] <> 1 then      # QT1[3] is gcd
                return QT1;          # return to ComputekP caller test for end
            fi;
            QTot := QT1;
            i := i+1;
        od;

        return QTot;
    end; # end of ComputekP(..) # handwritten: move-->?

    # Now we start EFactorsInt(..) proper

    # Step 0, i.e., things Sil & Tate left out:
    K := 17; # gross oversimplification for picking K
    factors := [];
    Q := [0,0,0];       # I need a way to make this a list of three.

    # Step 1
    g := GcdInt(n,6);

    if g = 3 then       # n better not be even!
        factors := Add(factors, 3);
        EFactorsInt(n/3); # the return fm EFactorsInt is lost?
    fi;
    
    #handle perfect powers
    p := SmallestRootInt(n);
    if p<n then
        while 1<n do
            Append(factors, EFactorsInt(p) );
            n := n/p;
        od;
        Sort(factors);
        return factors;
    fi;

    # Step 2
    b := 70;
    repeat
        if b > 1000 then
            b := 1;
                 K := K + 9;         ## where did this number come from??
        else
            b := b+1;
        fi;
        x1 := 2;
        y1 := 1;
        
        # Step 3
        
        c := EuclideanRemainder(y1^2 - x1^3 - b*x1, n);
        
        # Step 4
        d := 4*b^3 + 27*c^2;
        g := GcdInt(d, n); ## why was this underlined?
        
        # Step 5
        i := 1;
        k := 1;
        while i < Minimum(K, 1000) do
            k := Lcm(k,i);
            i := i+1;
        od;
        
        #Step 6
        Print("\nCalling ComputekP\n");
        Q := ComputekP(n, x1, y1, x1, y1); ## why do I start out with doubling??
        
        # Step 7
        # This looks at GCD returned by computekP, computes new b, k, x1, y1
    until 1 < Q[3] and Q[3] < n;
    Add(factors, Q[3]);
    EndTime := Runtime();
    return(factors);
end;
