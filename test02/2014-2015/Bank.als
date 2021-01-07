sig Account {}
abstract sig Transaction { amount: Int }
sig Deposit, Withdrawal extends Transaction {}

sig Client {
	accounts: some Account, 
	withdrawPrivileges: set Account,
	balance: Account set -> lone Int,
	transactions: Account one -> set Transaction
}

pred invariants[c: Client]{
	all ac: c.accounts | ac.(c.balance) >= 0 -- the balance of an account should never be lower than 0
	c.withdrawPrivileges in c.accounts-- a client can only withdraw from accounts she has access to
	(c.balance).Int in c.accounts-- a client only has balance from accounts she has access to
}

pred withdraw[c, c': Client, a: Account, qty: Int, t: Transaction]{
	--pre-conditions
	a in c.accounts
	a in c.withdrawPrivileges
	a.(c.balance) >= qty 

	--post-conditions
	a in c'.accounts
	a in c'.withdrawPrivileges
	a.(c'.balance) = a.(c.balance).minus[qty]
	a.(c'.balance) >= 0
	c'.transactions = c.transactions + a->t
}

fun totalBalance[c: Client] : Int {
	sum a: c.accounts | a.(c.balance)
}

assert withdraw_preserves_invariants {
	all c, c': Client, account: Account, qty: Int, t: Transaction |
		(invariants[c] and withdraw[c,c',account, qty, t] ) => ( invariants[c'] )
}

check withdraw_preserves_invariants

run {} for 6