
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
	batteryLevel=<100
	peopleOnBoard<=maxPeople
	maxPeople=5
	peopleOnBoard>=0
}
//Define the abstract state of a car
abstract sig State{ }

//Define specific states of a car
sig AvailableState extends State{ }
sig BrokenState extends State{ }
sig InUseState extends State{ }
sig ReservedState extends State{ }
sig OnChargeState extends State{ }

//Define a safe area
sig SafeArea{
	position: Position,
	occupiedParkingLots: Int,
	totalOutlets: Int
}	
{
	occupiedParkingLots >= 0
	totalOutlets > 5 and totalOutlets < 20
	totalOutlets >= occupiedParkingLots
}
//Define a charging area
sig ChargingArea extends SafeArea{
	carsInCharge: set Car
} 
{
	carsInCharge.state in OnChargeState
	#carsInCharge <= totalOutlets
	occupiedParkingLots = #carsInCharge

}
//Define a user
sig User{
	carInUse: lone Car,
	reservation: lone Reservation
}
{
	//If a user is riding a car then he can not have a reservation and viceversa
	#carInUse>0 => #reservation=0	
	#reservation>0 => #carInUse=0 
	carInUse != none => carInUse.state in InUseState
}
//Define a Reservation
sig Reservation{
	user: User,
	car: Car
}
{
	car.state in ReservedState
}
//Define a Ride
sig Ride{
	user: User,
	car: Car,
	time: Int, 
	cost: Int, 
	moneySavingOption: Bool, 
	initialPosition: Position,
	finalPosition: Position,
	pluggedIn:Bool,
	discount: Int,
	extraCharge:Int
}
{
	time > 0
	cost > 0
	cost = computeCost[1,time]
	discount >= 0
	extraCharge >= 0
	initialPosition != finalPosition
	car.state in InUseState
	initialPosition in (SafeArea.position + ChargingArea.position)
	finalPosition in (SafeArea.position + ChargingArea.position)
	car.batteryLevel = computeBatteryLevel[time] 
}
//Define a position
sig Position{
	lat: Int,
	long: Int
} 
{
	lat > 0
	lat < 8 
	long > 0
	long < 8
}


/***   FACTs   ***/


// Each car can be used exclusively from a single user at a time
fact {
	all disjoint u1, u2: User | u1.carInUse & u2.carInUse = none
}
// Each reservation has a unique car
fact{
	all r1,r2:Reservation| r1&r2 = none => r1.car & r2.car = none
}
//There can't be multiple users with the same reservation
fact{
	all u1:User|  (u1.reservation != none) => ( no u2:User| (u2 & u1 = none) and u1.reservation = u2.reservation)
}
//Each car in use is assigned to only one ride
fact{
	all disjoint r1,r2:Ride| r1.car & r2.car = none
}
//Each user is either on a ride or reserves a car
fact{
	Ride.user & Reservation.user = none
}
//If the car is reserved or in available state then its charge is at 100%
fact{
	all c:Car|(c.state in ReservedState or c.state in AvailableState) => c.batteryLevel=100
}
//If the car is InUseState it must have at least one person on board 	
fact{
	all c:Car|(c.state in InUseState) <=> c.peopleOnBoard>0
}
//If the car is InUseState, its charge is different than 0 and 100 (Constraint added for readability)
fact{
	all c:Car|(c.state in InUseState) => c.batteryLevel !=100 and c.batteryLevel!=0
}
//If a car is on charge its batteryLevel is less than 100 (Constraint added for readability)
fact{
	all c:Car|(c.state in OnChargeState) => c.batteryLevel <100
}
//Cars are always locked unless they're inUseState
fact{
	all c:Car|(c.locked = False) <=> c.state in InUseState
}
//Cars that are OnChargeState are in a chargingArea
fact{
	no c:Car|(c.state in OnChargeState) and c.location not in ChargingArea.position
}
//All cars not riding are in a safe area or in a charging area
fact{
	all c:Car|(c.state not in InUseState) <=> ( c.location in SafeArea.position or c.location in ChargingArea.position)
}
//All cars inUseState are assigned to a ride
fact{
	all c:Car|(c.state in InUseState) => c in Ride.car 
}
//A user on ride can park in a SafeArea only if there is at least one free parking lot
fact{
	all r:Ride,s:SafeArea|(r.finalPosition in s.position ) => (s.totalOutlets > s.occupiedParkingLots)
}
//A user on ride can park in a ChargingArea only if there is at least one free parking lot
fact{
	all r:Ride,c:ChargingArea|(r.finalPosition in c.position ) => (c.totalOutlets > c.occupiedParkingLots)	
}
//A user that plugs the car in the power grid after a ride is in ChargingArea
fact{
	all r:Ride|(r.pluggedIn = True) => r.finalPosition in ChargingArea.position
}
//If user has a discount he can not have an extraCharge
fact{
	all r:Ride|(r.discount != 0) => (r.extraCharge = 0)
}
//If user has an extraCharge he can not have a discount
fact{
	all r:Ride|(r.extraCharge != 0) => (r.discount = 0)
}
//A user gets a 10% discount on the last ride if and only if he's accompanied by at the least two people
fact{
	all r:Ride|(r.car.peopleOnBoard > 2 and r.car.batteryLevel < 50 and r.pluggedIn = False ) <=> r.discount = 10
}
//A user gets a 20% discount on the last ride if and only if the batteryLevel is greater than 50% at the end of the ride
fact{
	all r:Ride|(r.car.batteryLevel > 50 and r.pluggedIn = False ) <=> r.discount = 20
}
//A user gets a 30% discount on the last ride if takes care of plugging the car in the power grid at the end of the ride
fact{
	all r:Ride|(r.pluggedIn = True) <=> r.discount = 30
}
//A user gets a 30% discount on the last ride and the system guarantees a uniform distribution of cars among the SafeAreas if the user activates the MoneySavingOption
fact{
	all r:Ride|(r.moneySavingOption = True) => r.discount = 30 and (all disjoint s1,s2:SafeArea| s1.occupiedParkingLots = s2.occupiedParkingLots)
}
//A user gets a 30% extraCharge on the last ride if the batteryLevel is lower than 20% at the end of the ride
fact{
	all r:Ride|(r.car.batteryLevel < 20) => r.extraCharge = 30
}
//A user gets a 30% extraCharge on the last ride if he parks the car in a spot which is more than 3 km far from the nearest ChargingArea
fact{
	all r:Ride| all c:ChargingArea| distance[r.finalPosition,c.position,3] = True => r.extraCharge = 30
}
//The sets of possible values for the discount and extraCharge are finite
fact{
	all r:Ride|(r.discount = 10 or r.discount = 20 or r.discount = 30 or r.discount = 0) and (r.extraCharge = 0 or r.extraCharge = 30)
}
//Each ride has only one user
fact{
	all r1:Ride,r2:Ride| (r1 & r2 = none) => (r1.user & r2.user = none)
}
//Each car is either on a ride or reserved
fact{
	Ride.car & Reservation.car = none
}
//For each reservation, the user of the reserved car is whom reserved the car
fact{
	all r:Reservation| r.user.reservation = r 
}
//Each car must have a state
fact{
	all s:State| (s != none) => (some c:Car| c.state = s)
}


//This function returns true if the distance between the two given positions is greater than range, else false
fun distance(p1:Position,p2:Position,range:Int): Bool{
	(add[mul[minus[p1.lat,p2.lat],minus[p1.lat,p2.lat]],mul[minus[p1.long,p2.long],minus[p1.long,p2.long]]]) > mul[range,range] implies True else False
}
//This function returns the cost of a ride given the fare and the time
fun computeCost(fare:Int,time:Int):Int{
	mul[fare,time]
}
//This function returns the batteryLevel of a car given the time of the ride
fun computeBatteryLevel(time:Int):Int{
	minus[100,mul[time,1]]
}


//Each user who is riding a car can not have a reservation at the same time
assert RideOrReserve{
	all u:User|(u.carInUse != none) => (no r:Reservation | r.user = u)
}
//If a car is broken then it can not be riding
assert BrokenCarNotRiding{
	all c:Car|(c.state in BrokenState) => (no r:Ride| r.car = c)
}
//If a user takes care of plugging the car in the power grid he is rewarded with 30% discount on the last ride
assert PluggingTheCarIsGood{
	all r:Ride|(r.pluggedIn = True) => r.discount = 30
}


pred showWorld{
	#User>1
	#Ride>1
	#Reservation>1
	#Car>1
	#ChargingArea>1
	
}

run showWorld for 5 but 8 int

//check RideOrReserve for 8 int
//check BrokenCarNotRiding for 8 int
//check PluggingTheCarIsGood for 8 int
