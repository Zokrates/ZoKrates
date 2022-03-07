// SPDX-License-Identifier: MIT
pragma solidity ^0.8.10;

contract SimpleStorage {
    Var myVariable;

    struct Var {
        uint v;
    }

    function set(Var memory x) public {
        myVariable = x;
    }

    function get() public view returns (uint) {
        return myVariable.v;
    }
}
