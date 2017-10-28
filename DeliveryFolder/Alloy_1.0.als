open util/boolean

--SIGNATURES

sig Name{}

sig User {
	name: one Name,
	surname:one Name,
	age: one Int,
	username: one Name,
	email: one Name,
	password: one Name,
	preferences : one Preferences,
	calendar : one Calendar,
	drivingLicence : lone DrivingLicence}
{calendar.user = this and preferences.user = this and drivingLicence.user = this
	age >0}

sig DrivingLicence{
	id:one Name,
	user : one User}
{ user.drivingLicence = this}

sig Calendar {
	currentDate: Date,
	user : one User,
	date : some Date}
{user.calendar = this}
	

sig Date {
	day: one Int,
	month: one Int,
	year: one Int,
	event : set Event,
	strike : set Strike,
	journey : one Journey
}
{all e : event | e.date = this
journey.date = this
day >0 month >0  year >0}
	


sig Location{
	latitude: one Int, //should be float
	longitude: one Int //should be float
}{ latitude >0 longitude >0}

sig Preferences {
	maxWalkingTime : one Int,
	maxBikingTime: one Int,
	fixedLunchTime : one Int,
	user : one User,
	eco: one Bool,
	ownedCar: one Bool,
	ownedBike: one Bool}
{user.preferences = this maxWalkingTime >0 maxBikingTime >0 fixedLunchTime >0
maxWalkingTime = maxBikingTime maxBikingTime = fixedLunchTime}


sig Event{
 	date : one Date,
	location : one Location,
	timeRange : one TimeRange}
{this in date.event}


sig Journey {
	date : one Date,
	preferences : one Preferences,
	route : some Route}
{date.event != none
 date.journey = this}

sig Route{
	transportMean : one TransportMean,
	event : one Event
}
{transportMean != none <=> this in Journey.route
transportMean not in Strike.transportMean
#this = #event}


sig Strike{
	transportMean:  one TransportMean}

abstract sig TransportMean{}
sig Car extends TransportMean{}
sig Bike extends TransportMean{}
sig Walking extends TransportMean{}
sig PublicTransport extends TransportMean{}


sig TimeRange{}




--FACTS

fact usernamesAreUnique {
	all u1, u2 : User | u1 != u2 => u1.username != u2.username}

fact emailsAreUnique{
	all u1,u2 : User | u1 != u2 => u1.email != u2.email}

fact differentEventsForDiffDates{
	all disjoint d1, d2 : Date | d1.event & d2.event = none}

fact differentStrikeForDiffDates{
	all disjoint d1, d2 : Date | d1.strike & d2.strike = none
}

fact allDatesForSameCalendar{
Calendar.date = Date}
 

fact onlyOneJourneyPerDate{
	all disjoint j1, j2 : Journey | j1.date &  j2.date = none}

fact strikeOfTransport{
	}

fact strikesAreDifferent{
	all disjoint s1, s2 : Strike | s1 in Date.strike and s2 in Date.strike}

fact  sameTimeRangeAndEvents{
	#TimeRange = #Event}

fact sameRouteAndEvent{
	#Route = #Event}

fact differentRouteforDifferentEvents{
	all disjoint r1,r2 :Route |r1.event &r2.event = none }

fact transportMeanInfluencedByStrikes{
all d : Date | all j : Journey | d in j.date and j in d.journey => j.route.transportMean & d.strike.transportMean = none}

fact timeRangeAreUniquePerEvent{
	all disjoint e1,e2 : Event | e1.timeRange != e2.timeRange}

fact routeForTheEventOfTheCorrespondingJourney{
all d : Date | all j : Journey | d in j.date and j in d.journey=> j.route.event in d.event
}



--PREDICATES
pred addEvent [e1, e2 : Event, d1, d2: Date]{
    e2 in d1.event
	e1 not in d1.event 
	e1.timeRange != e2.timeRange
	implies
	 d2.event = d1.event + e1}

pred deleteEvent [e: Event, d1,d2: Date]{
	e in d1.event 	
	implies 
	d2.event = d1.event -e}

pred insertEco [u:User, p:Preferences]{
	p in u.preferences and u in p.user
	 implies
	 p.eco = True}

pred modifyMaxWalkingTime [ p1, p2: Preferences]{
	 p1.maxWalkingTime != p2.maxWalkingTime}

pred modifyMaxBikingTime [ p1, p2: Preferences]{
	 p1.maxBikingTime != p2.maxBikingTime}

pred fixLunchTime[p1,p2 : Preferences]{
	p1.fixedLunchTime != p2.fixedLunchTime
}

pred journeyRefresh [j1,j2 : Journey, r1,r2,r3,r4 : Route, e1,e2,e3 : Event, d : Date]{
	r1 in j1.route and r2  in j1.route
	j1 in d.journey and d in j1.date
	(e1 + e2 + e3) in d.event
	implies 
	r1 not in j2.route or r2 not in j2.route => r3  in j2.route or r4 in j2.route
	j1 not in d.journey
	j2 in d.journey and d in j2.date 
	(e1 + e2 + e3) in d.event
	
}



run {} for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run addEvent{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run deleteEvent{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run insertEco{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run modifyMaximumWalkingTime{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run modifyMaximumBikingTime{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run fixLunchTime{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey

run journeyRefresh{}for 4 but exactly 1 User, exactly 3 Location, exactly 2 Strike, exactly 2 Journey




