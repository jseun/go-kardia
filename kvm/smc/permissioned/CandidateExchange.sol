pragma solidity ^0.4.24;

// CandidateExchange forward candidate info requests and results to targeted private chains
contract CandidateExchange {
    event IncomingRequest(string email, string fromOrgID, string toOrgID);
    event FulfilledRequest(string email, string response, string fromOrgID, string toOrgID);

    // This function is used to notify chain B a request come from chain A by using event
    // IncomingRequest. Dual node Kardia - B will catch this event and response
    function forwardRequest(string _email, string _fromOrgID, string _toOrgID) public {
        emit IncomingRequest(_email, _fromOrgID, _toOrgID);
    }

    // This function is used to notify chain A a candidate info responded by chainB by using event
    // FulfilledRequest. Dual node Kardia - A will catch this event and store it into
    // CandidateDB of chain A
    function forwardResponse(string _email, string _response, string _fromOrgID, string _toOrgID) public {
        emit FulfilledRequest(_email, _response, _fromOrgID, _toOrgID);
    }
}
