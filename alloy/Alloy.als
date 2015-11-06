//////////// SIGS ////////////////

sig Stringa { }

sig Address {
        streetName: one Stringa,
        streetNr: one Int,
        gpsCoords: one Stringa,
        zone: one Zone
} {
	streetNr > 0
}

sig Zone {
        id: one Int,
        name: one Stringa
} {
	id > 0
}

sig Ride {
   id: one Int,
   status: one RideStatus,
   startTime: one Int,
   endTime: lone Int,
   totalNrPeople: one Int
} {
	id > 0
	startTime > 0
	endTime = none or endTime > 0
	totalNrPeople > 0
}

abstract sig Call {
        id: one Int,
        timeRegistration: one Int,
        startPoint: one Address,
        endPoint: one Address,
        nrPeople: one Int,
        paymentMethod: set PaymentMethod,
        ride: one Ride
} {
	id > 0
	timeRegistration > 0
	nrPeople > 0
}

sig Reservation extends Call {
        isShareable: one Bool,
}

sig Request extends Call {}

sig Customer {
        id : one Int,
        name : one Stringa,
        email : one Stringa,
        mobilePhone : one Stringa,
        call: set Call
}

sig TaxiAllocationDaemon {
	queues: set TaxiQueue
}

sig TaxiHandler {
        ride: one Ride,
        serve: set Customer,
        taxiQueue: one TaxiQueue,
        allocate: lone Taxi // zero if no taxis are assigned yet
} {
	allocate in taxiQueue.taxis
}

sig Taxi {
        id: one Int,
        licencePlate: one Stringa,
        taxiDriverName: one Stringa,
        numberOfSeats: one Int,
        status: one TaxiStatus, 
        paymentMethodsAccepted: set PaymentMethod
} {
	id > 0
	numberOfSeats > 0
}

sig TaxiQueue {
        taxis: set Taxi
}

//////////// ENUMS ////////////////

enum Bool {
        TRUE,
        FALSE
}

enum TaxiStatus {
        AVAILABLE,
        UNAVAILABLE,
        ACCEPTING,
        BUSY
}

enum RideStatus {
        PENDING,
        ASSIGNED,
        INRIDE,
        COMPLETED
}

enum PaymentMethod {
	CASH,
	POS
}

// note on dates: UNIX timestamps are used for convenience purposes

//////////// FACTS ////////////////
// at least a zone in the city
fact atLeastAZone {
	#Zone >= 1
}

// there is always an allocation daemon running
fact taxiAllocationDaemonRunning {
	#TaxiAllocationDaemon = 1
}

// an UNAVAILABLE taxi driver must not appear in any queue
fact unavailableTaxiDriversNoQueue {
	all t : Taxi | t.status = UNAVAILABLE implies 
		(no q : TaxiQueue | t in q.taxis)
}

// if there is no taxiHandler pointing to a taxi driver, that driver must not be BUSY and ACCEPTING
fact noBusyDriversWithoutTaxiHandlers {
	all t : Taxi | 
		(no th : TaxiHandler | th.allocate = t) implies (t.status != BUSY)
}



// bijection between taxiHandlers and rides
fact bijectionTaxiHandlerRide {
	(all th: TaxiHandler | one r : Ride | th.ride = r) && // each taxihandler has just a ride
	(all r: Ride | lone th: TaxiHandler | th.ride = r) // each ride belongs to just a taxihandler if it still exists
}


// each TaxiHandler has just a reference to one of the queues of the TaxiAllocationDaemon
fact consistentZoneQueues {
	all th: TaxiHandler |
		one tad : TaxiAllocationDaemon | 
			th.taxiQueue in tad.queues
}

// there are no queues outside the ones in the TaxiAllocationDaemon set
fact noExternalQueues {
	all q : TaxiQueue |
		one tad : TaxiAllocationDaemon | 
			q in tad.queues
}

// number of zones = number of queues
fact equalZoneQueues {
	#{ Zone } =  #TaxiAllocationDaemon.queues
}

// if a ride is in PENDING status, no taxi must be allocated yet
fact pendingRideNoAllocation {
	all r : Ride | r.status = PENDING implies
		( (no th: TaxiHandler | th.ride = r ) || (one th : TaxiHandler | th.ride = r &&
		       #th.allocate = 0) ) 
	and
	all r : Ride | (r.status = INRIDE || r.status = ASSIGNED) implies
		( one th : TaxiHandler | th.ride = r && #th.allocate = 1) 
}



// if a ride is in COMPLETE status, then the corresponding taxiHandler must not exist anymore
fact noTaxiHandlerForCompleteRides {
	all r : Ride | r.status = COMPLETED implies
		(no th : TaxiHandler | th.ride = r)
}

// if a ride is in INRIDE status, then the taxi driver must be busy
fact inRideTaxiDriver {
        all r : Ride | (r.status = INRIDE || r.status = ASSIGNED) implies 
                one th : TaxiHandler | th.ride = r && 
		   #th.allocate = 1 && 
		   th.allocate.status = BUSY
}

// each ride must end after it started
fact noNegativeTimeRides {
	all r: Ride | (r.status = COMPLETED implies r.startTime < r.endTime) && 
	(r.status != COMPLETED implies #r.endTime = 0)
}

// if there's a PENDING call, there must not be 2 taxis in ACCEPTING status
fact oneAcceptingTaxiForACall {
        all r : Ride | r.status = PENDING implies 
                ( (no th: TaxiHandler | th.ride = r) or (one th : TaxiHandler | th.ride = r && some t : Taxi | t in th.taxiQueue.taxis && t.status = ACCEPTING) )
}

fact acceptingTaxiRelatedToAPendingRide {
	all t : Taxi | t.status = ACCEPTING implies 
		one th : TaxiHandler | th.ride.status = PENDING && t in th.taxiQueue.taxis
}

// a driver must be in just a queue
fact driverInOneQueueOnly {
	(no q1, q2 : TaxiQueue | 
             q1 != q2 &&
	   some t : Taxi | t in q1.taxis && t in q2.taxis) &&
	( all t2 : Taxi | some q : TaxiQueue | t2 in q.taxis )
}

// there is at least a taxi available in each queue
fact atLeastOneTaxiAvailableInEveryQueue {
    all queue : TaxiQueue | 
	some t : Taxi | 
		t in queue.taxis && t.status = AVAILABLE		// but at least one of them is available
}

// each ride is not duplicated
fact noDuplicatedRides {
   no r1, r2 : Ride | 
	r1.id = r2.id && 
	r1 != r2
}

// each zone is not duplicated
fact noDuplicatedZones {
   no z1, z2 : Zone | 
	z1.id = z2.id && 
	z1 != z2
}

// each taxi is not duplicated
fact noDuplicatedTaxis {
   no t1, t2 : Taxi | 
	(t1.id = t2.id || t1.licencePlate = t2.licencePlate) && 
	t1 != t2
}

// Each street must be in the same zone
// NOTE: can fail if a street is very long
fact addressConsistentZone {
   all a1 : Address | no a2 : Address |
	a1.streetName = a2.streetName 
	//&& a1.streetNr = a2.streetNr
	&& a1.zone != a2.zone
}

// there are no more than one reservation for a not sharable ride
fact notSharableRideNumberOfPassengers {
   no r1, r2 : Reservation | 
	r1.isShareable = FALSE && r2.isShareable = FALSE &&
	r1.ride = r2.ride &&
	r1 != r2
}

// the number of people for a certain ride must equal the sum of all people that booked that ride through several reservations
fact numberOfSeatsForARide {
   all r : Ride |
	all c : Call |
		c.ride = r && // for all calls relative to a ride
		(sum p : Call | #p.nrPeople) = #r.totalNrPeople // the sum of people in all calls ...
}

// number of people in a ride must be <= than the taxi availability
fact taxiCanActuallyTakeRide {
	all th : TaxiHandler |
		th.allocate.status = ACCEPTING or th.allocate.status = BUSY implies
			(#th.ride.totalNrPeople <= #th.allocate.numberOfSeats)
}
 
// all requests have been made before the ride actually started
fact noRequestsAfterRide {
   all c : Call |
	c.timeRegistration < c.ride.startTime
}

// the allocated taxi is compatible with the chosen payment method
fact POSEnabled {
   all c : Call | 
	one th : TaxiHandler | th.ride = c.ride &&
	th.allocate.paymentMethodsAccepted & c.paymentMethod != none
}

// all taxis must accept cash as a valid payment method
fact cashTaxi {
	all t: Taxi |
	   CASH in t.paymentMethodsAccepted
}

fact oneRideForATaxi {
	all t : Taxi | all th1, th2 : TaxiHandler | (th1 != th2 && t = th1.allocate implies t != th2.allocate) 
}

fact pendingEqualAccepting {
	#{r : Ride | r.status = PENDING} >= #{ t : Taxi | t.status = ACCEPTING } 
}

//////////// ASSERTIONS ////////////////

// ######## A1 ########
// There are no queues anywhere with no available taxis (it also means that there is always a taxi in each queue)
assert noAllUnavailableTaxisInAQueue {
    all q : TaxiQueue |
	some t : Taxi | t in q.taxis && t.status = AVAILABLE
}

// WORKING
//check noAllUnavailableTaxisInAQueue for 7

// ######## A2 ########
// for every ride with an allocated taxi, there must be an equal number of busy taxi driver
assert equalNumberAllocationsBusyDrivers {
	#{th : TaxiHandler | #th.allocate = 1} = #{t : Taxi | t.status = BUSY}  
}

// WORKING
//check equalNumberAllocationsBusyDrivers for 7

// ######## A3 ########
// it there are more than call for a ride, then it must be a shared reservation
assert sharedReservations {
	all c1, c2: Call | (c1 != c2 && c1.ride = c2.ride implies 
		(c1 in Reservation and c2 in Reservation and c1.isShareable = TRUE and c2.isShareable = TRUE) )
}

// WORKING
//check sharedReservations for 15

// ######## A4 ########


//////////// PREDICATES ////////////////

pred show(){ 
	#TaxiAllocationDaemon = 1
	#Address = 3
	#Zone = 2
	#Ride = 5
	#TaxiQueue = #Zone
	#TaxiHandler = #{r : Ride | r.status != COMPLETED }
	#Taxi >= #Zone + 1
	#{ r : Ride | r.status = INRIDE } >= 1
	#{ r : Ride | r.status = PENDING } = 2 
	#{ t : Taxi | t.status = ACCEPTING } >= 1
	#Customer >= 2	
}	

//ok
//run show for 15

pred shareable {
	/*#TaxiAllocationDaemon = 1
	#Address = 3
	#Ride = 5
	#Reservation >= 2
	#Customer >= 5
	#TaxiHandler = #{r : Ride | r.status != COMPLETED }
	#Zone = 2
	#TaxiQueue = #Zone
	#Taxi >= 6*/
}

run shareable for 15


