pragma solidity >=0.8.0;

contract Token {
    uint256 public totalSupply;
    mapping (address => uint256) public balanceOf;
    mapping (address => mapping (address => uint256)) public allowance;
    
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    error ERC20InsufficientBalance(address sender, uint256 balance, uint256 needed);
    error ERC20InvalidSender(address sender);
    error ERC20InvalidReceiver(address receiver);
    error ERC20InsufficientAllowance(address spender, uint256 allowance, uint256 needed);
    error ERC20InvalidApprover(address approver);
    error ERC20InvalidSpender(address spender);

    constructor(uint256 _totalSupply) {
        totalSupply = _totalSupply;
        balanceOf[msg.sender] = _totalSupply;
    }

    function _transfer(address from, address to, uint256 value) internal {
        require(from != address(0), ERC20InvalidSender(from));
        require(to != address(0), ERC20InvalidReceiver(to));
        _update(from, to, value);
    }

    function _update(address from, address to, uint256 value) internal {
        if(from == address(0)) {
            balanceOf[to] = balanceOf[to] + value;
            totalSupply += value;
        } else if (to == address(0)) {
            require(value <= balanceOf[from], ERC20InsufficientBalance(from, balanceOf[from], value));
            balanceOf[from] = balanceOf[from] - value;
            totalSupply -= value;
        } else {
            require(value <= balanceOf[from], ERC20InsufficientBalance(from, balanceOf[from], value));
            balanceOf[from] = balanceOf[from] - value;
            balanceOf[to] = balanceOf[to] + value;
        }
        emit Transfer(from, to, value);
    }

    function _mint(address account, uint256 value) internal {
        _update(address(0), account, value);
    }

    function _burn(address account, uint256 value) internal {
        _update(account, address(0), value);
    }

    function _approve(address owner, address spender, uint256 value) internal {
        _approve(owner, spender, value, true);
    }

    function _approve(address owner, address spender, uint256 value, bool emitEvent) internal {
        require(owner != address(0), ERC20InvalidApprover(owner));
        require(spender != address(0), ERC20InvalidSpender(spender));
        allowance[owner][spender] = value;
        if (emitEvent) emit Approval(owner, spender, value);
    }

    function _spendAllowance(address owner, address spender, uint256 value) internal {
        require(value <= allowance[owner][spender], ERC20InsufficientAllowance(spender, allowance[owner][spender], value));
        if (allowance[owner][spender] != type(uint256).max) {
            uint256 new_value = allowance[owner][spender] - value;
            _approve(owner, spender, new_value, false);
        }
    }

    function transfer(uint256 value, address to) public returns (bool) {
        _transfer(msg.sender, to, value);
        return true;
    }

    function approve(address spender, uint256 value) public returns (bool) {
        if(spender != msg.sender) {
            _approve(msg.sender, spender, value);
        }
        return true;
    }

    function transferFrom(address from, address to, uint256 value) public returns (bool) {
        if(from != msg.sender) {
            _spendAllowance(from, msg.sender, value);
        }
        _transfer(from, to, value);
        return true;
    }

    function mint(address account, uint256 value) public returns(bool) {
        _mint(account, value);
        return true;
    }

    function burn(uint256 value) public returns(bool) {
        _burn(msg.sender, value);
        return true;
    }

    function burnFrom(address account, uint256 value) public returns(bool) {
        if(account != msg.sender) {
            _spendAllowance(account, msg.sender, value);
        }
        _burn(account, value);
        return true;
    }
}
