//////////// SIGS ////////////////

sig Address {
        streetName: one String,
        streetNr: one int,
        gpsCoords: one String,
        zone: one Zone
}

sig Zone {
        id: one int,
        name: one String,
        // numberOfTaxisAvailable : one int
}

sig Date {
        day: one int,
        month: one int,
        year: one int,
        hour: one int,
        min: one int
}

sig Ride {
   id: one int,
   status: one RideStatus,
   dateTimeRide: one Date,
   totalNrPeople: one int
}

abstract sig Call {
        id: one int,
        dateTimeRegistration: one Date,
        startPoint: one Address,
        endPoint: one Address,
        nrPeople: one int,
        paymentMethod: one int,
        ride: one Ride
} 

sig Reservation extends Call {
        isShareable: one Bool,
        desideredDateTime: one Date

}

sig Request extends Call {}

sig Customer {
        id : one int,
        name : one String,
        email : one String,
        mobilePhone : one String,
        call: set Call
}

sig TaxiAllocationDaemon {
	queues: set TaxiQueue
}

sig TaxiHandler {
        ride: one Ride,
        serve: set Customer,
        taxiQueue: one TaxiQueue,
        allocate: lone Taxi // zero if no taxis is assigned yet
} {
	allocate in taxiQueue.taxis
}

sig Taxi {
        id: one int,
        licencePlate: one String,
        taxiDriverName: one String,
        numberOfSeats: one int,
        status: one TaxiStatus
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

//////////// FACTS ////////////////

fact notifyAvailabilityOnlyWhenUnavailable {
//
}

fact atLeastOneTaxiInQueue {
        //some taxi : Taxi | taxi in contact
}

// se una ride e' inride, allora il suo tassista c'è e deve essere busy
fact correlationRideTaxiDriver {
        all r : Ride | r.status = INRIDE implies 
                one th : TaxiHandler | th.ride = r && #th.allocate = 1 && th.allocate.status = BUSY
}

// se una call e' pending, non ci devono essere 2 taxi che la accetteranno
fact oneAcceptingTaxiForACall {
        all r : Ride | r.status = PENDING implies 
                one th : TaxiHandler | th.ride = r && 
                        !(t1, t2: Taxi | t1 in th.taxiQueue.taxis && t2 in th.taxiQueue.taxis && 
                                t1.status = ACCEPTING && t2.status = ACCEPTING && t1 != t2)
}

// una notifica alla volta 
fact oneNotifyAtTimeForATaxiDriver {
//        all c : Call | c.status = PENDING implies 
//                one th : TaxiHandler | th.handle = c && 
//                        !(t1, t2: Taxi | t1 in th.contact && t2 in th.contact && 
//                                t1.status = ACCEPTING && t2.status = ACCEPTING && t1 != t2)
}

//almeno 1 taxi disponibile per ogni coda
fact atLeastOneTaxiAvailableInEveryQueue {
    all queue : TaxiQueue | 
	some t : Taxi | 
		t in queue &&
		t.status = AVAILABLE
}

fact noDuplicatedZones {
   no z1, z2 : Zone | 
	z1.id = z2.id && 
	z1 != z2
}

// NOTE: can fail if a street is very long (think of Viale Monza..)
fact addressConsistentZone {
   all a1 : Address | no a2 : Address |
	a1.streetName = a2.streetName 
	/*&& a1.streetNr = a2.streetNr*/ 
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
		c.ride = r &&
		(sum p : c | #c.nrPeople) = #r.totalNrPeople
}

 
