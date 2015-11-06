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
	endTime > 0
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
        desideredDateTime: one Int
} {
	desideredDateTime > 0
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


// bijection between taxiHandlers and rides
fact bijectionTaxiHandlerRide {
	(all th: TaxiHandler | one r : Ride | th.ride = r) && // each taxihandler has just a ride
	(all r: Ride | one th: TaxiHandler | th.ride = r) // each ride belongs to just a taxihandler
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
		one th : TaxiHandler | th.ride = r &&
		       #th.allocate = 0	
}

// if a ride is in INRIDE status, then the taxi driver must be busy
fact inRideTaxiDriver {
        all r : Ride | r.status = INRIDE implies 
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
                one th : TaxiHandler | th.ride = r && 
                        no t1, t2: Taxi | t1 in th.taxiQueue.taxis && t2 in th.taxiQueue.taxis && 
                                t1.status = ACCEPTING && t2.status = ACCEPTING && t1 != t2
}

// a driver must be in just a queue
fact driverInOneQueueOnly {
	no q1, q2 : TaxiQueue | 
             q1 != q2 &&
	   some t : Taxi | t in q1.taxis && t in q2.taxis 
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
// NOTE: can fail if a street is very long (think of Viale Monza..)
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


//////////// ASSERTIONS ////////////////

// ######## A1 ########
assert noAllUnavailableTaxisInAQueue {
    all q : TaxiQueue |
	some t : Taxi | t in q.taxis && t.status = AVAILABLE
}

// WORKING!
// check noAllUnavailableTaxisInAQueue for 25

// ######## A2 ########
// new assertions coming along

//////////// PREDICATES ////////////////
pred show(){ 
	// to be completed
}

//////////// RUN ////////////////

run show for 3
