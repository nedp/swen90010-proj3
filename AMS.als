/** Data types **/
sig UserID {}
// There is exactly one emergency userID
one sig EmergencyUser extends UserID {}

// There are three types of contacts, Friends, Insurer, and Emergeny.
// Users can give different permissions to different contact types.
abstract sig ContactTypes {}
one sig Friend, Insurer, Emergency extends ContactTypes {}

// Three types of data stored: number of foosteps, beats per minute,
// and location
sig Footsteps {}
sig BPM {}
sig GPSLocation {}

//A simple Boolean data type
abstract sig Boolean {}
one sig True, False extends Boolean {}


/** The system state **/
sig AMS {
    //The set of current users
    users : set UserID-EmergencyUser,

    //Records each user's friend, insurer
    friends : users->users,
    insurers : users->users,

    //Records each user's relevant data
    footsteps : users->Footsteps,
    vitals : users->BPM,
    locations : users->GPSLocation,

    // Records for each user the permissions given for each data type
    // and role. Many to many.
    footstepsPermissions : users->ContactTypes,
    vitalsPermissions : users->ContactTypes,
    locationsPermissions : users->ContactTypes,
}
{
    // Since every user has the single Emergency user as the
    // emergency contact, there's no reason to have it as a relation.

    // Nobody can be their own friend or insurer.
    all u, v : UserID | u = v implies (u->v) not in insurers+friends

    // The insurer always has permissions to read footsteps.
    all u : UserID | (u->Insurer) in footstepsPermissions
}

/** Initial state **/
pred init [ams : AMS] {
    no ams.users
}

/** Users and their social network **/
//Create a new user
pred CreateUser [ams, ams' : AMS, userID: one UserID] {
    userID not in ams.users
    ams'.users = ams.users + userID

    //Unchanged
    ams'.friends = ams.friends
    ams'.insurers = ams.insurers
    DataUnchanged [ams, ams']
}

//Update, remove, and read insurer information for a specific user
pred SetInsurer [ams, ams' : AMS, wearer, insurer: UserID] {
    wearer+insurer in ams.users
    ams'.insurers = ams.insurers ++ (wearer->insurer)

    //Unchanged
    ams'.users = ams.users
    ams'.friends = ams.friends
    DataUnchanged [ams, ams']
}

pred RemoveInsurer [ams, ams' : AMS, wearer : UserID] {
    some ams.insurers[wearer]
    ams'.insurers = ams.insurers - (wearer->UserID)

    //Unchanged
    ams'.users = ams.users
    ams'.friends = ams.friends
    DataUnchanged [ams, ams']
}

fun ReadInsurer [ams : AMS, wearer : UserID] : lone UserID {
    ams.insurers[wearer]
}

//Update, remove, and read friend information for a specific user
pred SetFriend [ams, ams' : AMS, wearer, friend: UserID] {
    wearer+friend in ams.users
    ams'.friends = ams.friends ++ (wearer->friend)

    //Unchanged:
    ams'.users = ams.users
    ams'.insurers = ams.insurers
    DataUnchanged [ams, ams']

}

pred RemoveFriend [ams, ams' : AMS, wearer : UserID] {
    some ams.friends[wearer]
    ams'.friends = ams.friends - (wearer->UserID)

    //Unchanged:
    ams'.users = ams.users
    ams'.insurers = ams.insurers
    DataUnchanged [ams, ams']
}

fun ReadFriend [ams : AMS, wearer : UserID] : lone UserID {
    ams.friends[wearer]
}

/** Data management **/
//Update relevant data
pred UpdateFootsteps [ams, ams' : AMS, wearer : UserID, newFootsteps : Footsteps] {
    wearer in ams.users
    ams'.footsteps = ams.footsteps ++ (wearer->newFootsteps)

    //Unchanged:
    ams'.vitals = ams.vitals
    ams'.locations = ams.locations
    UsersUnchanged [ams, ams']
}

pred UpdateVitals [ams, ams' : AMS, wearer : UserID, newVitals : BPM] {
    wearer in ams.users
    ams'.vitals = ams.vitals ++ (wearer->newVitals)

    //Unchanged:
    ams'.footsteps = ams.footsteps
    ams'.locations = ams.locations
    UsersUnchanged [ams, ams']
}

pred UpdateLocation [ams, ams' : AMS, wearer : UserID, newLocation : GPSLocation] {
    wearer in ams.users
    ams'.locations = ams.locations ++ (wearer->newLocation)

    //Unchanged:
    ams'.footsteps = ams.footsteps
    ams'.vitals = ams.vitals
    UsersUnchanged [ams, ams']
}

/** Models of "external" API calls **/
//ContactEmergency -- The external call specified in the 'Emergency' package in Assignment 1
pred ExternalContactEmergency [wearer : UserID, wearerLocation : GPSLocation, wearerVitals : BPM] {
    //Contact emergency services
}

/** Helper predicates **/
// Users and their social network are unchanged.
pred UsersUnchanged [ams, ams' : AMS] {
    ams'.users = ams.users
    ams'.friends = ams.friends
    ams'.insurers = ams.insurers
}

// Data about users isunchanged.
pred DataUnchanged [ams, ams' : AMS] {
    ams'.footsteps = ams.footsteps
    ams'.vitals = ams.vitals
    ams'.locations = ams.locations
}

// Permissions for users are unchanged.
pred PermissionsUnchanged [ams, ams' : AMS] {
    ams'.footstepsPermissions = ams.footstepsPermissions
    ams'.vitalsPermissions = ams.vitalsPermissions
    ams'.locationsPermissions = ams.locationsPermissions
}

run CreateUser for 3

// Creating a new user does not add any friends/insurers
assert NoUserChange {
    all ams, ams' : AMS, userID : UserID |
        CreateUser[ams, ams', userID] => ams.friends = ams'.friends and ams.insurers = ams'.insurers
}
check NoUserChange for 3
