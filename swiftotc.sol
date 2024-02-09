// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    constructor() {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), msg.sender);
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(owner() == msg.sender, "Caller is not the owner");
        _;
    }

    function transferOwnership(address newOwner) public onlyOwner {
        require(newOwner != address(0), "New owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

pragma solidity ^0.8.0;

abstract contract ReentrancyGuard {
    bool private _notEntered;

    constructor() {
        _notEntered = true;
    }

    modifier nonReentrant() {
        require(_notEntered, "Reentrant call");
        _notEntered = false;
        _;
        _notEntered = true;
    }
}

pragma solidity ^0.8.0;

interface IERC20 {
    function balanceOf(address account) external view returns (uint256);
    function allowance(address owner, address spender) external view returns (uint256);
    function transfer(address recipient, uint256 amount) external returns (bool);
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);
}

contract OTCSmartContract is ReentrancyGuard, Ownable {
    struct Order {
        uint256 orderId;
        address seller;
        address buyer;
        address tokenToSell;
        uint256 amountToSell;
        address tokenToBuy;
        uint256 amountToBuy;
        uint8 status; // 0 = open, 1 = finalized, 2 = cancelled
    }

    Order[] public orders;
    address public treasury_address;
    mapping(address => bool) public whitelistedTokens;
    uint256 public feePercentage = 1; // Default fee 1%

    function setTreasuryAddress(address _treasuryAddress) public onlyOwner {
        treasury_address = _treasuryAddress;
    }

    function whitelistToken(address _token, bool _whitelisted) public onlyOwner {
        whitelistedTokens[_token] = _whitelisted;
    }

    function setFeePercentage(uint256 _feePercentage) public onlyOwner {
        require(_feePercentage <= 5, "Fee cannot be more than 5%");
        feePercentage = _feePercentage;
    }

    event OrderMade(
        uint256 indexed orderId,
        address indexed seller,
        address tokenToSell,
        uint256 amountToSell,
        address tokenToBuy,
        uint256 amountToBuy
    );
    event OfferAccepted(uint256 indexed orderId, address indexed buyer);
    event OrderCanceled(uint256 indexed orderId, address indexed seller);

    constructor() {}

   function createOrder(
    address _tokenToSell,
    uint256 _amountToSell,
    address _tokenToBuy,
    uint256 _amountToBuy
) public nonReentrant {
    require(
        IERC20(_tokenToSell).balanceOf(msg.sender) >= _amountToSell,
        "Insufficient token balance"
    );
    require(
        IERC20(_tokenToSell).allowance(msg.sender, address(this)) >=
            _amountToSell,
        "Contract not allowed to transfer tokens"
    );

    IERC20(_tokenToSell).transferFrom(
        msg.sender,
        address(this),
        _amountToSell
    );

    uint256 orderId = orders.length;
    orders.push(
        Order({
            orderId: orderId,
            seller: msg.sender,
            buyer: address(0),
            tokenToSell: _tokenToSell,
            amountToSell: _amountToSell,
            tokenToBuy: _tokenToBuy,
            amountToBuy: _amountToBuy,
            status: 0
        })
    );

    emit OrderMade(
        orderId,
        msg.sender,
        _tokenToSell,
        _amountToSell,
        _tokenToBuy,
        _amountToBuy
    );
}

function acceptOrder(uint256 _orderId) public nonReentrant {
    require(orders[_orderId].status == 0, "Order not open");
    require(
        IERC20(orders[_orderId].tokenToBuy).balanceOf(msg.sender) >=
            orders[_orderId].amountToBuy,
        "Insufficient token balance"
    );
    require(
        IERC20(orders[_orderId].tokenToBuy).allowance(msg.sender, address(this)) >=
            orders[_orderId].amountToBuy,
        "Contract not allowed to transfer tokens"
    );

    bool isWhitelisted = whitelistedTokens[orders[_orderId].tokenToSell];
    uint256 feeAmount = 0;
    uint256 transferAmountToSeller = orders[_orderId].amountToBuy;

    if (!isWhitelisted) {
        feeAmount = orders[_orderId].amountToBuy * feePercentage / 100;
        transferAmountToSeller -= feeAmount;
    }

    if(feeAmount > 0) {
        IERC20(orders[_orderId].tokenToBuy).transferFrom(
            msg.sender,
            treasury_address,
            feeAmount
        );
    }

    IERC20(orders[_orderId].tokenToBuy).transferFrom(
        msg.sender,
        orders[_orderId].seller,
        transferAmountToSeller
    );

    orders[_orderId].buyer = msg.sender;
    orders[_orderId].status = 1; // Finalized

    emit OfferAccepted(_orderId, msg.sender);
}

    function cancelOrder(uint256 _orderId) public nonReentrant {
        require(_orderId < orders.length, "Order does not exist");
        Order storage order = orders[_orderId];

        require(order.seller == msg.sender, "Only seller can cancel");
        require(order.status == 0, "Order already accepted or finalized");

        IERC20(order.tokenToSell).transfer(order.seller, order.amountToSell);

        order.status = 2; // Status 2 for canceled orders

        emit OrderCanceled(_orderId, msg.sender);
    }

    function orderCount() public view returns (uint256) {
        return orders.length;
    }

    function getOrder(uint256 _orderId) public view returns (Order memory) {
        require(_orderId < orders.length, "Order does not exist");
        return orders[_orderId];
    }
}
