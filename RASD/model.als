open util/boolean

//Define the car
sig Car{
	state: one State,
	batteryLevel: Int,
	peopleOnBoard: Int,
	maxPeople: Int,
	location: Position,
	locked: Bool
}
{
	batteryLevel>=0
	batteryLevel<=100
	peopleOnBoard<=maxPeople
	maxPeople=5
	peopleOnBoard>=0
	state=ReservedState => batteryLevel=100 // ??
	state=InUseState <=> peopleOnBoard>0
}

//Define the abstract state of a car
abstract sig State{ }

//Define specific states of a car
sig AvailableState extends State{ }
sig NotAvailableState extends State{ }
sig InUseState extends State{ }
sig ReservedState extends State{ }
sig OnChargeState extends State{ }

//Define a safe area
sig SafeArea{
	position: Position
}	

//Define a charging area
sig ChargingArea extends SafeArea{
	carsInCharge: set Car,
	availableOutlets: Int
} 
{
	#carsInCharge<= availableOutlets
}

sig User{
	carInUse: lone Car,
	reservation: lone Reservation
}
{
	#carInUse>0 => #reservation=0	
	#reservation>0 => #carInUse=0
}

sig Reservation{
	user: User,
	car: Car
}
{
	car.locked=False
}

sig Ride{
	user: User,
	car: Car,
	time: Int, // ride time in minutes
	cost: Int, // Float
	moneySavingOption: Bool, //necessario?
	initialPosition: Position,
	finalPosition: Position
}{
	time > 0
	cost > 0
}

sig Position{
	lat: Int,
	long: Int
} //DEFINIRE FUNZIONE PER CALCOLARE DISTANZA?
{
	lat > 0
	long > 0
	// WHAT ELSE?
}


/***   FACTs   ***/

// The cars currently used are the only in the 'InUseState' 
fact {
	all u: User, c: u.carInUse | c.state = InUseState
}

// Each car can be used exclusively from a single user at a time
fact {
	no disjoint u1, u2: User | u1.carInUse & u2.carInUse != none
}
// Each reservation has a unique car
fact{
	no disjoint r1,r2:Reservation| r1.car & r2.car !=none
}
//Each user who has a reservation, is assigned to only one reservation
fact{
	no disjoint u1,u2:User| u1.reservation & u2.reservation !=none and #u1.reservation=#u2.reservation and #u1.reservation=1
}
//Each car in use is assigned to only one ride
fact{
	no disjoint r1,r2:Ride| r1.car & r2.car !=none
}
//Each user is either on a ride or reserves a car
fact{
	no r1:Ride,r2:Reservation| r1.user & r2.user !=none
}
//Each car is either on a ride or reserved
fact{
	no r1:Ride,r2:Reservation| r1.car & r2.car !=none
}
//Each ride has only one user
/*fact{
	no disjoint r1:Ride,r2:Ride| r1.user & r2.user !=none
}*/
// For each reservation, the car reserved is in ReservedState
fact {
	all r: Reservation, c: r.car | c.state = ReservedState 
}

fact {
	all r: Reservation, u: r.user | u.reservation=r
}


pred showWorld{
	#User>0
	#Ride>0
	#Reservation>0
	#Car>0
}
run showWorld for 3







