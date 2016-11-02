//Define the car
sig Car{
	state: one State,
	batteryLevel: Int,
	peopleOnBoard: Int, //NECESSARIO?
	maxPeople: Int,
	location: Position
}
{
	batteryLevel>=0
	batteryLevel<=100
	//CONTROLLI SUL NUMERO DI PERSONE...
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
	CarInUse: lone Car,
}

sig Reservation{
	user: User,
	car: Car,
	expiringTime: Time
}

sig Time {
	hour: Int,
	minute: Int
}

sig Ride{
	user: User,
	car: Car,
	time: Int, //time expressed in minutes
	cost: Int, //should be FLOAT
	initialPosition: Position,
	finalPosition: Position
}

sig Position{
	lat: Int,
	long: Int
} //DEFINIRE FUNZIONE PER CALCOLARE DISTANZA?

/* FACT */
fact {
	all u: User, c: u.CarInUse| c.state=InUseState
	 
}



pred show{}
run show for 3







