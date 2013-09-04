exception InvalidInput;
fun odd (n) = 
if n=0 then false else even (n-1) 
and even (n) = 
if n=0 then true else odd (n-1); 

fun square(x:real)= x*x;
fun linear(x:real)=(2.0*x)+3.0;
fun cubeplusone(x:real)=x*x*x+1.0;

fun sum(a:real,it:int,h:real,F)=
if it<=0 then 0.0
else if odd(it) then 4.0*F(a+real(it)*h)+sum(a,it-1,h,F)
else 2.0*F(a+real(it)*h)+sum(a,it-1,h,F);


fun simpson(a:real,b:real,n:int,F) =
if n <= 0 then raise InvalidInput
else
let val h= (b-a) / real(2*n)
in
(h / 3.0) * (F(a)+F(b)+sum(a,(2*n)-1,h,F))
end;

print "Executing Simpson for Linear function F(x) = 2x + 3 with a=0.0, b=1.0,n=100 ";
simpson(0.0,1.0,100,linear);

print "Executing Simpson for square function F(x) = x*x with a=0.0, b=1.0,n=100 ";
simpson(0.0,1.0,100,square);

print "Executing Simpson for cubeplusone function F(x) = x*x*x+1 with a=0.0, b=1.0,n=100 ";
simpson(0.0,1.0,100,cubeplusone);

print "Executing Simpson for cubeplusone function F(x) = x*x*x+1 with a=0.0, b=1.0 and Invalid n= -1 ";
simpson(0.0,1.0,~1,cubeplusone);

