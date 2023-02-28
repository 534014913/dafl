/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial

*/

method m (a: int) returns (b: int) 
{
  var x, y: int;
  // { x == 50 }
  assume x == 50;	
  // { (x < 3 ==> x == 89) && (!(x < 3) ==> 50) }
  assert (x < 3 ==> x == 89) && (!(x < 3) ==> x == 50);
  if x < 3 {
		// { x == 89 }
	  assert x == 89 ;
		// { x + 1 + 10 == 100 }
		x, y := x + 1, 10;
 	  // { x + y == 100 }
		assert x + y == 100;
	} else { 
		// { x == 50 }	
	  assert x == 50 ;
		// { x + x == 100 }
		y := x; 
	  // { x + y == 100 }
		assert x + y == 100 ;
	}
	// { x + y == 100 }
  assert x + y == 100;
}


method Abs(x: int) returns (y: int)
  ensures x < 0 ==> y == -x
  ensures x >= 0 ==> y == x
{
  if (x < 0) 
    { y := -x; }
  else
    { y := x; }
}

method main(x:int) returns (abs:int)
  ensures abs >= x
{
  abs := Abs(x);
  assert abs >= x;

}

method Test1(x: int)
{

  var v := Abs(x);
  assert x > 0 ==> v == x;

  var v1 := Abs(3);
  assert v1 == 3;

  var v2 := Abs(-3);
  assert v2 == 3;

}

/*
function abs(x: int): int
{
  if x < 0 then -x else x
}

method Test2(x: int)
{
  var v := Abs(x);
  assert v == abs(x);
}
*/