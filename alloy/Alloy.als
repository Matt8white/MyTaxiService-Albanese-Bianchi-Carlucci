//////////// SIGS ////////////////

sig Address {
	streetName: one String,
	streetNr: one int,
	gpsCoords: one String,
	has: one Zone
}

sig Zone {
	id: one int,
	name: one String,
	numberOfTaxisAvailable : one int
}

sig Date {
	day: one int,
	month: one int,
	year: one int,
	hour: one int,
	minutes: one int
}

abstract sig Call {
	ID: one int,
	status: one CallStatus,
	dateTime: one Date,
	accepted: one Bool,
	startPoint: one Address,
	endPoint: one Address,
	nrPeople: one int,
	paymentMethod: one int,
	has: set Address,
	has: set Date
} 

sig Customer {
	id : one int,
	name : one String,
	email : one String,
	mobilePhone : one String,
	call: set Call
}

sig TaxiHandler {
	handle: one Call,
	serve: set Customer,
	contact: one TaxiQueue,
	allocate: one Taxi
} 

sig Taxi {
	id: one int,
	licencePlate: one String,
	taxiDriverName: one String,
	numberOfSeats: one int,
	seatsAvailable: one int,
	status: one TaxiStatus
}

sig Reservation extends Call {
	isShareable: one Bool,
	desideredDateTime: one Date

}

sig Request extends Call {}

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

enum CallStatus {
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
	some taxi : Taxi | taxi in contact
}

fact correlationRideTaxiDriver {
	all c : Call | c.status = INRIDE implies 
		one th : TaxiHandler | th.handle = c && th.allocate.status = BUSY
}

fact oneAcceptingTaxiForACall {
	all c : Call | c.status = PENDING implies 
		one th : TaxiHandler | th.handle = c && 
			!(t1, t2: Taxi | t1 in th.contact && t2 in th.contact && 
				t1.status = ACCEPTING && t2.status = ACCEPTING && t1 != t2)
}

