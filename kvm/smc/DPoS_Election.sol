// Compiler: remix: 0.5.4+commit.9549d8ff
pragma solidity ^0.5.0;

contract DPoS_Election {
    
    /** The validator applicant needs to provide his info in order to participate in the election:
     * - Validator's PubKey, e.g. "6fcae76a8b37cba"
     * - Validator's name, e.g. "Jon Snow"
     * - Initial self-bond amount, e.g 100 kai coins
     * - Dividend ratio: the ratio in which it is sharing the profit with its stakers, e.g. "40/60"
     * - Validator's description (Optional)
     **/
    struct ValidatorInfo {
        string pubKey; 
        string name;
        uint selfStake;
        string dividendRatio;
        string description;
    }
    
    struct Candidate {
        uint stakes;
        uint ranking;
        bool exist;
        ValidatorInfo info;
        uint numVoters;
        Voter[] myVoters; // maps voter address to staked amount
    }
    
    struct Voter {
        address payable voter;
        uint stakedAmount;
    }
    
    // State variables
    address public owner;
    bool public initCalled;
    bool public electionEnded;
    uint public numValidators; 
    uint public numCandidates;
    mapping (address => Candidate) candidates;
    address[] public rankings; // keeps track of candidate rankings, position 1 is the highest
    address[] public validatorList; // stores list of validators after vote ended

    // Events
    event Signup(address candidate, uint stakes);
    event VoteCast(address voter, address candidate, uint stakes);
    event CandidateRanking(address candidate, uint position);
    event Refund(address voter, uint value);
    
    
    // Modifiers
    modifier onlyOwner{
        require(msg.sender == owner, "Only the owner can call the function");
        _;
    }
    modifier checkValue {
        require(msg.value > 0, "Value of stake must be positive");
        _;
    }
    modifier electionNotEnded {
        require(!electionEnded, "The vote is not ended yet");
        _;
    }
    modifier initialized {
        require(initCalled, "The contract must be initialized");
        _;
    }
    
    // Functions
    /** Initialize the contract. This function can only be called once **/
    function init(uint n) public {
        require(!initCalled, "Init can only be called once");
        require(n > 0, "Number of validators must be positive");
        owner = msg.sender;
        electionEnded = false;
        numValidators = n;
        validatorList = new address[](numValidators);
        rankings.push(address(0x0)); // dummy address at position 0
        initCalled = true;
    }
    
    /** Allows candidate to sign up and stake for itself **/
    function signup(string memory pubKey, string memory name, string memory ratio, string memory description) 
        public payable initialized electionNotEnded checkValue {
        if (candidates[msg.sender].exist) {
            revert("Candidate already exists");
        }
        numCandidates++;
        candidates[msg.sender].stakes = msg.value;
        candidates[msg.sender].info = ValidatorInfo(pubKey, name, msg.value, ratio, description);
        candidates[msg.sender].exist = true;

        // Update ranking if necessary
        rankings.push(msg.sender);
        candidates[msg.sender].ranking = rankings.length - 1;
        sortByRanking(rankings.length-1);
        emit Signup(msg.sender, msg.value);
    }
    
    /** Allows voter to delegate their KAI to stake for a candidate.
     *  A voter can vote for multiple candidates by calling the function multiple times **/
    function vote(address candAddress) public payable initialized electionNotEnded checkValue{
        if (!candidates[candAddress].exist) {
            revert("Candidate does not exist");
        }
        // Update candidate votes
        candidates[candAddress].stakes += msg.value;
        
        // Update voter staked amount
        candidates[candAddress].myVoters.push(Voter(msg.sender, msg.value));
        candidates[candAddress].numVoters += 1;

        // Update ranking if necessary
        sortByRanking(candidates[candAddress].ranking);
        emit VoteCast(msg.sender, candAddress, msg.value);
    }
    
    /** Sorts the rankings array assuming the rest of the array is already sorted
     *  and the position of a candidate can only move up to higher rank.
     *  Returns the candidate's position after the sort **/ 
    function sortByRanking(uint index) private {
        for (uint i = index; i > 1; i--) {
            if (candidates[rankings[i]].stakes <= candidates[rankings[i-1]].stakes) {
                break;
            }
            // Swap the candidate up one rank 
            candidates[rankings[i]].ranking = i-1;
            candidates[rankings[i-1]].ranking = i;
            
            address temp = rankings[i];
            rankings[i] = rankings[i-1];
            rankings[i-1] = temp;
        }
    }
    
    /** Returns a candidate **/ 
    function getCandidateStake(address candAddress) public view returns (uint){
        return candidates[candAddress].stakes;
    }
    
    /** Returns the current ranking of a candidate **/ 
    function getCandidateRanking(address candAddress) public returns (uint){
        uint position = candidates[candAddress].ranking;
        assert(rankings[position] == candAddress);
        emit CandidateRanking(candAddress, position);
        return position;
    }
    
    /** Returns the current list of all rankings **/ 
    function getCurrentRankings() public view returns (address[] memory) {
        return rankings;
    }
    
    /** Returns the list of result after vote ended **/ 
    function getValidatorList() public view returns (address[] memory) {
        return validatorList;
    }
    
    /** Ends the vote and copies final result to validatorList and
     *  refund for voters whose candidates failed to be elected
     **/ 
    function endElection() public payable initialized electionNotEnded onlyOwner{
        electionEnded = true;
        
        // Copy final result to validatorList
        for (uint i = 1; i <= numValidators && i < rankings.length; i++) {
            validatorList[i-1] = rankings[i];
        }
        
        // Refund to voters
        for (uint j = numValidators + 1; j <= numCandidates; j++) {
            Candidate memory c = candidates[rankings[j]];
            for (uint k = 0; k < c.numVoters; k++) {
                transferTo(c.myVoters[k].voter, c.myVoters[k].stakedAmount);
                candidates[rankings[j]].myVoters[k].stakedAmount = 0;
            }
        }
    }
    
    /** Returns the current balance of the address **/ 
    function getBalance(address addr) view public returns(uint) {
        return addr.balance;
    }
    
    /** Transfers amount to recipient **/ 
    function transferTo(address payable recipient, uint amount) public payable {
        recipient.transfer(amount);
        emit Refund(recipient, amount);
    }
}
