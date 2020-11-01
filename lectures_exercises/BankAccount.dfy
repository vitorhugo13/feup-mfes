
class BankAccount {
    var balance: real;
    
    //class invariant
    predicate Valid()
      reads this //premissao de leitura de objetos
    {
        balance >= 0.0
    }
 
    constructor (initialBalance: real)
      requires initialBalance >= 0.0
      ensures Valid() //class invariant, funciona como uma pós condição(no final do construtor tem de se verificar)
      ensures balance == initialBalance
    {
        balance := initialBalance;
    }
 
    function method getBalance() : real
      reads this
      requires Valid()
    {
      balance
    }

    method deposit(amount : real)
      modifies this //premisao para alteração
      requires Valid() && amount > 0.0 //class invariant em methods tem de se verificar no inicio e no fim
      ensures Valid() && balance == old(balance) + amount
    {
        balance := balance + amount;
    }

    method withdraw(amount : real)
      requires Valid() && 0.0 < amount <= balance
      modifies this //premisao para alteração
      ensures Valid() && balance == old(balance) - amount
    {
        balance := balance - amount;
    }

    method transfer(amount : real, destination: BankAccount)
      requires 0.0 < amount <= balance && destination != this
      requires Valid() && destination.Valid()
      modifies this, destination
      ensures Valid() && destination.Valid()  
      ensures balance == old(balance) - amount
      ensures destination.balance == old(destination.balance) + amount
    {
        this.balance := this.balance - amount;
        destination.balance:= destination.balance + amount;
    }
}

// A simple test case.
method testBankAccount()
{
    var a := new BankAccount(10.0);
    assert a.getBalance() == 10.0;

    var b := new BankAccount(0.0);
    assert b.getBalance() == 0.0;

    a.deposit(10.0);
    assert a.getBalance() == 20.0;

    a.withdraw(5.0);
    assert a.getBalance() == 15.0;

    a.transfer(15.0, b);
    assert a.getBalance() == 0.0;
    assert b.getBalance() == 15.0;

    b.withdraw(10.0);
    assert b.getBalance() == 5.0;    
}
