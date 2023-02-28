/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa
   
   Instructor: Cesare Tinelli
*/

// Bank account example showcasing the idea of (heap) frames

class Trans {
  var total: int;

  constructor ()
    ensures total == 0
  {
    total := 0;
  }

  method add(n: nat)
    modifies this
    ensures total == old(total) + n
  {
    total := total + n;
  }
}


class Account
{
  // public (abstract) variables
  ghost var Balance: int;         // the current balance of the account.
  ghost var Frame: set<object>;   // set of all objects (in the heap)
                                  // that methods can read or modify

  // private variables
  var deposits: Trans;    // stores the total amount of deposits
  var withdrawls: Trans;  // stores the total amount of withdrawls

  function Valid(): bool
    reads this, Frame
  {
    // concrete state invariants
    && deposits != withdrawls
    
    // Frame invariants
    && Frame == {this, deposits, withdrawls}  
	  
    // connection between abstract and concrete state
    && Balance == deposits.total - withdrawls.total
  }

  constructor ()
    ensures Valid()
    ensures Balance == 0
  {
    deposits := new Trans();
    withdrawls := new Trans();
    
    // Ghost code
    Balance := 0;
    // establishes the initial frame
    Frame := {this, deposits, withdrawls};
  }

  method GetBalance() returns (b: int)
    requires Valid();
    ensures Valid();
    ensures b == Balance;
  {
    b := deposits.total - withdrawls.total;
  }

  method Deposit(a: nat)
    modifies Frame;
    requires Valid();
    ensures Valid();
    ensures Balance == old(Balance) + a;
  {
    deposits.add(a);
    
    // ghost code
    Balance := Balance + a;
    Frame := {this, deposits, withdrawls};

  }

  method Withdraw(a: nat)
    modifies Frame;
    requires Valid();
    ensures Valid();
    ensures Balance == old(Balance) - a;
  {
    withdrawls.add(a);
    
    // ghost code
    Balance := Balance - a;
    Frame := {this, deposits, withdrawls};
  }
}

