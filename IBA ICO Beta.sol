pragma solidity ^0.4.21;

/**
 * RealMath: fixed-point math library, based on fractional and integer parts.
 * Using int128 as real88x40, which isn't in Solidity yet.
 * 40 fractional bits gets us down to 1E-12 precision, while still letting us
 * go up to galaxy scale counting in meters.
 * Internally uses the wider int256 for some math.
 *
 * Note that for addition, subtraction, and mod (%), you should just use the
 * built-in Solidity operators. Functions for these operations are not provided.
 *
 * Note that the fancy functions like sqrt, atan2, etc. aren't as accurate as
 * they should be. They are (hopefully) Good Enough for doing orbital mechanics
 * on block timescales in a game context, but they may not be good enough for
 * other applications.
 *
 * INFORMATION: This library has been modified to provide internal functions
 * instead of public ones. This is because of the need to compile those
 * functions into the destination contract to work properly.
 */

library RealMath {

    /**
     * How many total bits are there?
     */
    int256 constant REAL_BITS = 128;

    /**
     * How many fractional bits are there?
     */
    int256 constant REAL_FBITS = 40;

    /**
     * How many integer bits are there?
     */
    int256 constant REAL_IBITS = REAL_BITS - REAL_FBITS;

    /**
     * What's the first non-fractional bit
     */
    int128 constant REAL_ONE = int128(1) << REAL_FBITS;

    /**
     * What's the last fractional bit?
     */
    int128 constant REAL_HALF = REAL_ONE >> 1;

    /**
     * What's two? Two is pretty useful.
     */
    int128 constant REAL_TWO = REAL_ONE << 1;

    /**
     * And our logarithms are based on ln(2).
     */
    int128 constant REAL_LN_TWO = 762123384786;

    /**
     * It is also useful to have Pi around.
     */
    int128 constant REAL_PI = 3454217652358;

    /**
     * And half Pi, to save on divides.
     * TODO: That might not be how the compiler handles constants.
     */
    int128 constant REAL_HALF_PI = 1727108826179;

    /**
     * And two pi, which happens to be odd in its most accurate representation.
     */
    int128 constant REAL_TWO_PI = 6908435304715;

    /**
     * What's the sign bit?
     */
    int128 constant SIGN_MASK = int128(1) << 127;

    /**
     * Convert an integer to a real. Preserves sign.
     */
    function toReal(int88 ipart) internal pure returns (int128) {
        return int128(ipart) * REAL_ONE;
    }

    /**
     * Convert a real to an integer. Preserves sign.
     */
    function fromReal(int128 real_value) internal pure returns (int88) {
        return int88(real_value / REAL_ONE);
    }

    /**
     * Round a real to the nearest integral real value.
     */
    function round(int128 real_value) internal pure returns (int128) {
        // First, truncate.
        int88 ipart = fromReal(real_value);
        if ((fractionalBits(real_value) & (uint40(1) << (REAL_FBITS - 1))) > 0) {
            // High fractional bit is set. Round up.
            if (real_value < int128(0)) {
                // Rounding up for a negative number is rounding down.
                ipart -= 1;
            } else {
                ipart += 1;
            }
        }
        return toReal(ipart);
    }

    /**
     * Get the absolute value of a real. Just the same as abs on a normal int128.
     */
    function abs(int128 real_value) internal pure returns (int128) {
        if (real_value > 0) {
            return real_value;
        } else {
            return -real_value;
        }
    }

    /**
     * Returns the fractional bits of a real. Ignores the sign of the real.
     */
    function fractionalBits(int128 real_value) internal pure returns (uint40) {
        return uint40(abs(real_value) % REAL_ONE);
    }

    /**
     * Get the fractional part of a real, as a real. Ignores sign (so fpart(-0.5) is 0.5).
     */
    function fpart(int128 real_value) internal pure returns (int128) {
        // This gets the fractional part but strips the sign
        return abs(real_value) % REAL_ONE;
    }

    /**
     * Get the fractional part of a real, as a real. Respects sign (so fpartSigned(-0.5) is -0.5).
     */
    function fpartSigned(int128 real_value) internal pure returns (int128) {
        // This gets the fractional part but strips the sign
        int128 fractional = fpart(real_value);
        if (real_value < 0) {
            // Add the negative sign back in.
            return -fractional;
        } else {
            return fractional;
        }
    }

    /**
     * Get the integer part of a fixed point value.
     */
    function ipart(int128 real_value) internal pure returns (int128) {
        // Subtract out the fractional part to get the real part.
        return real_value - fpartSigned(real_value);
    }

    /**
     * Multiply one real by another. Truncates overflows.
     */
    function mul(int128 real_a, int128 real_b) internal pure returns (int128) {
        // When multiplying fixed point in x.y and z.w formats we get (x+z).(y+w) format.
        // So we just have to clip off the extra REAL_FBITS fractional bits.
        return int128((int256(real_a) * int256(real_b)) >> REAL_FBITS);
    }

    /**
     * Divide one real by another real. Truncates overflows.
     */
    function div(int128 real_numerator, int128 real_denominator) internal pure returns (int128) {
        // We use the reverse of the multiplication trick: convert numerator from
        // x.y to (x+z).(y+w) fixed point, then divide by denom in z.w fixed point.
        return int128((int256(real_numerator) * REAL_ONE) / int256(real_denominator));
    }

    /**
     * Create a real from a rational fraction.
     */
    function fraction(int88 numerator, int88 denominator) internal pure returns (int128) {
        return div(toReal(numerator), toReal(denominator));
    }

    // Now we have some fancy math things (like pow and trig stuff). This isn't
    // in the RealMath that was deployed with the original Macroverse
    // deployment, so it needs to be linked into your contract statically.

    /**
     * Raise a number to a positive integer power in O(log power) time.
     * See <https://stackoverflow.com/a/101613>
     */
    function ipow(int128 real_base, int88 exponent) internal pure returns (int128) {
        if (exponent < 0) {
            // Negative powers are not allowed here.
            revert();
        }

        // Start with the 0th power
        int128 real_result = REAL_ONE;
        while (exponent != 0) {
            // While there are still bits set
            if ((exponent & 0x1) == 0x1) {
                // If the low bit is set, multiply in the (many-times-squared) base
                real_result = mul(real_result, real_base);
            }
            // Shift off the low bit
            exponent = exponent >> 1;
            // Do the squaring
            real_base = mul(real_base, real_base);
        }

        // Return the final result.
        return real_result;
    }

    /**
     * Zero all but the highest set bit of a number.
     * See <https://stackoverflow.com/a/53184>
     */
    function hibit(uint256 val) internal pure returns (uint256) {
        // Set all the bits below the highest set bit
        val |= (val >>  1);
        val |= (val >>  2);
        val |= (val >>  4);
        val |= (val >>  8);
        val |= (val >> 16);
        val |= (val >> 32);
        val |= (val >> 64);
        val |= (val >> 128);
        return val ^ (val >> 1);
    }

    /**
     * Given a number with one bit set, finds the index of that bit.
     */
    function findbit(uint256 val) internal pure returns (uint8 index) {
        index = 0;
        // We and the value with alternating bit patters of various pitches to find it.

        if (val & 0xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA != 0) {
            // Picth 1
            index |= 1;
        }
        if (val & 0xCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCCC != 0) {
            // Pitch 2
            index |= 2;
        }
        if (val & 0xF0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0 != 0) {
            // Pitch 4
            index |= 4;
        }
        if (val & 0xFF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00FF00 != 0) {
            // Pitch 8
            index |= 8;
        }
        if (val & 0xFFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000FFFF0000 != 0) {
            // Pitch 16
            index |= 16;
        }
        if (val & 0xFFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000FFFFFFFF00000000 != 0) {
            // Pitch 32
            index |= 32;
        }
        if (val & 0xFFFFFFFFFFFFFFFF0000000000000000FFFFFFFFFFFFFFFF0000000000000000 != 0) {
            // Pitch 64
            index |= 64;
        }
        if (val & 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000000000000000000000000000 != 0) {
            // Pitch 128
            index |= 128;
        }
    }

    /**
     * Shift real_arg left or right until it is between 1 and 2. Return the
     * rescaled value, and the number of bits of right shift applied. Shift may be negative.
     *
     * Expresses real_arg as real_scaled * 2^shift, setting shift to put real_arg between [1 and 2).
     *
     * Rejects 0 or negative arguments.
     */
    function rescale(int128 real_arg) internal pure returns (int128 real_scaled, int88 shift) {
        if (real_arg <= 0) {
            // Not in domain!
            revert();
        }

        // Find the high bit
        int88 high_bit = findbit(hibit(uint256(real_arg)));

        // We'll shift so the high bit is the lowest non-fractional bit.
        shift = high_bit - int88(REAL_FBITS);

        if (shift < 0) {
            // Shift left
            real_scaled = real_arg << -shift;
        } else if (shift >= 0) {
            // Shift right
            real_scaled = real_arg >> shift;
        }
    }

    /**
     * Calculate the natural log of a number. Rescales the input value and uses
     * the algorithm outlined at <https://math.stackexchange.com/a/977836> and
     * the ipow implementation.
     *
     * Lets you artificially limit the number of iterations.
     *
     * Note that it is potentially possible to get an un-converged value; lack
     * of convergence does not throw.
     */
    function lnLimited(int128 real_arg, int max_iterations) public pure returns (int128) {
        if (real_arg <= 0) {
            // Outside of acceptable domain
            revert();
        }

        if (real_arg == REAL_ONE) {
            // Handle this case specially because people will want exactly 0 and
            // not ~2^-39 ish.
            return 0;
        }

        // We know it's positive, so rescale it to be between [1 and 2)
        int128 real_rescaled;
        int88 shift;
        (real_rescaled, shift) = rescale(real_arg);

        // Compute the argument to iterate on
        int128 real_series_arg = div(real_rescaled - REAL_ONE, real_rescaled + REAL_ONE);

        // We will accumulate the result here
        int128 real_series_result = 0;

        for (int88 n = 0; n < max_iterations; n++) {
            // Compute term n of the series
            int128 real_term = div(ipow(real_series_arg, 2 * n + 1), toReal(2 * n + 1));
            // And add it in
            real_series_result += real_term;
            if (real_term == 0) {
                // We must have converged. Next term is too small to represent.
                break;
            }
            // If we somehow never converge I guess we will run out of gas
        }

        // Double it to account for the factor of 2 outside the sum
        real_series_result = mul(real_series_result, REAL_TWO);

        // Now compute and return the overall result
        return mul(toReal(shift), REAL_LN_TWO) + real_series_result;

    }

    /**
     * Calculate a natural logarithm with a sensible maximum iteration count to
     * wait until convergence. Note that it is potentially possible to get an
     * un-converged value; lack of convergence does not throw.
     */
    function ln(int128 real_arg) internal pure returns (int128) {
        return lnLimited(real_arg, 100);
    }

    /**
     * Calculate e^x. Uses the series given at
     * <http://pages.mtu.edu/~shene/COURSES/cs201/NOTES/chap04/exp.html>.
     *
     * Lets you artificially limit the number of iterations.
     *
     * Note that it is potentially possible to get an un-converged value; lack
     * of convergence does not throw.
     */
    function expLimited(int128 real_arg, int max_iterations) public pure returns (int128) {
        // We will accumulate the result here
        int128 real_result = 0;

        // We use this to save work computing terms
        int128 real_term = REAL_ONE;

        for (int88 n = 0; n < max_iterations; n++) {
            // Add in the term
            real_result += real_term;

            // Compute the next term
            real_term = mul(real_term, div(real_arg, toReal(n + 1)));

            if (real_term == 0) {
                // We must have converged. Next term is too small to represent.
                break;
            }
            // If we somehow never converge I guess we will run out of gas
        }

        // Return the result
        return real_result;

    }

    /**
     * Calculate e^x with a sensible maximum iteration count to wait until
     * convergence. Note that it is potentially possible to get an un-converged
     * value; lack of convergence does not throw.
     */
    function exp(int128 real_arg) internal pure returns (int128) {
        return expLimited(real_arg, 100);
    }

    /**
     * Raise any number to any power, except for negative bases to fractional powers.
     */
    function pow(int128 real_base, int128 real_exponent) internal pure returns (int128) {
        if (real_exponent == 0) {
            // Anything to the 0 is 1
            return REAL_ONE;
        }

        if (real_base == 0) {
            if (real_exponent < 0) {
                // Outside of domain!
                revert();
            }
            // Otherwise it's 0
            return 0;
        }

        if (fpart(real_exponent) == 0) {
            // Anything (even a negative base) is super easy to do to an integer power.

            if (real_exponent > 0) {
                // Positive integer power is easy
                return ipow(real_base, fromReal(real_exponent));
            } else {
                // Negative integer power is harder
                return div(REAL_ONE, ipow(real_base, fromReal(-real_exponent)));
            }
        }

        if (real_base < 0) {
            // It's a negative base to a non-integer power.
            // In general pow(-x^y) is undefined, unless y is an int or some
            // weird rational-number-based relationship holds.
            revert();
        }

        // If it's not a special case, actually do it.
        return exp(mul(real_exponent, ln(real_base)));
    }

    /**
     * Compute the square root of a number.
     */
    function sqrt(int128 real_arg) internal pure returns (int128) {
        return pow(real_arg, REAL_HALF);
    }

    /**
     * Compute the sin of a number to a certain number of Taylor series terms.
     */
    function sinLimited(int128 real_arg, int88 max_iterations) public pure returns (int128) {
        // First bring the number into 0 to 2 pi
        // TODO: This will introduce an error for very large numbers, because the error in our Pi will compound.
        // But for actual reasonable angle values we should be fine.
        real_arg = real_arg % REAL_TWO_PI;

        int128 accumulator = REAL_ONE;

        // We sum from large to small iteration so that we can have higher powers in later terms
        for (int88 iteration = max_iterations - 1; iteration >= 0; iteration--) {
            accumulator = REAL_ONE - mul(div(mul(real_arg, real_arg), toReal((2 * iteration + 2) * (2 * iteration + 3))), accumulator);
            // We can't stop early; we need to make it to the first term.
        }

        return mul(real_arg, accumulator);
    }

    /**
     * Calculate sin(x) with a sensible maximum iteration count to wait until
     * convergence.
     */
    function sin(int128 real_arg) public pure returns (int128) {
        return sinLimited(real_arg, 15);
    }

    /**
     * Calculate cos(x).
     */
    function cos(int128 real_arg) public pure returns (int128) {
        return sin(real_arg + REAL_HALF_PI);
    }

    /**
     * Calculate tan(x). May overflow for large results. May throw if tan(x)
     * would be infinite, or return an approximation, or overflow.
     */
    function tan(int128 real_arg) public pure returns (int128) {
        return div(sin(real_arg), cos(real_arg));
    }

    /**
     * Calculate atan(x) for x in [-1, 1].
     * Uses the Chebyshev polynomial approach presented at
     * https://www.mathworks.com/help/fixedpoint/examples/calculate-fixed-point-arctangent.html
     * Uses polynomials received by personal communication.
     * 0.999974x-0.332568x^3+0.193235x^5-0.115729x^7+0.0519505x^9-0.0114658x^11
     */
    function atanSmall(int128 real_arg) public pure returns (int128) {
        int128 real_arg_squared = mul(real_arg, real_arg);
        return mul(mul(mul(mul(mul(mul(
            - 12606780422,  real_arg_squared) // x^11
            + 57120178819,  real_arg_squared) // x^9
            - 127245381171, real_arg_squared) // x^7
            + 212464129393, real_arg_squared) // x^5
            - 365662383026, real_arg_squared) // x^3
            + 1099483040474, real_arg);       // x^1
    }

    /**
     * Compute the nice two-component arctangent of y/x.
     */
    function atan2(int128 real_y, int128 real_x) public pure returns (int128) {
        int128 atan_result;

        // Do the angle correction shown at
        // https://www.mathworks.com/help/fixedpoint/examples/calculate-fixed-point-arctangent.html

        // We will re-use these absolute values
        int128 real_abs_x = abs(real_x);
        int128 real_abs_y = abs(real_y);

        if (real_abs_x > real_abs_y) {
            // We are in the (0, pi/4] region
            // abs(y)/abs(x) will be in 0 to 1.
            atan_result = atanSmall(div(real_abs_y, real_abs_x));
        } else {
            // We are in the (pi/4, pi/2) region
            // abs(x) / abs(y) will be in 0 to 1; we swap the arguments
            atan_result = REAL_HALF_PI - atanSmall(div(real_abs_x, real_abs_y));
        }

        // Now we correct the result for other regions
        if (real_x < 0) {
            if (real_y < 0) {
                atan_result -= REAL_PI;
            } else {
                atan_result = REAL_PI - atan_result;
            }
        } else {
            if (real_y < 0) {
                atan_result = -atan_result;
            }
        }

        return atan_result;
    }
}


/*
Template copied from:
https://github.com/ConsenSys/Token-Factory/blob/master/contracts/StandardToken.sol

This implements ONLY the standard functions and NOTHING else.
For a token like you would want to deploy in something like Mist, see HumanStandardToken.sol.

If you deploy this, you won't have anything useful.

Implements ERC 20 Token standard: https://github.com/ethereum/EIPs/issues/20
.*/

contract StandardToken {

    // An array holding IBA balances for all user accounts.
    mapping (address => uint256) internal balances;

    // An array holding allowances to make transfers between accounts.
    mapping (address => mapping (address => uint256)) internal allowed;

    // Total IBA unit supply (hard cap)
    uint256 public totalSupply;

    // Emitted after successfull transfer.
    event Transfer (
        address indexed _from, address indexed _to, uint256 _value
    );

    // Emitted after _owner allows _spender to transfer _value of IBA wei.
    event Approval (
        address indexed _owner, address indexed _spender, uint256 _value
    );

    // Allows user to transfer _value of IBA wei to the _to account.
    function transfer (address _to, uint256 _value)
        public returns (bool success)
    {
        if (balances[msg.sender] >= _value && _value > 0) {
            balances[msg.sender] -= _value;
            balances[_to] += _value;
            emit Transfer(msg.sender, _to, _value);
            return true;
        } else {
            return false;
        }
    }

    // Allows any user to execute transfer between accounts,
    // where allowance for given _value has been set between users.
    function transferFrom (address _from, address _to, uint256 _value)
        public returns (bool success)
    {
        if (
            balances[_from] >= _value && allowed[_from][msg.sender] >=
            _value && _value > 0
        ) {
            balances[_to] += _value;
            balances[_from] -= _value;
            allowed[_from][msg.sender] -= _value;
            emit Transfer(_from, _to, _value);
            return true;
        } else {
            return false;
        }
    }

    // Returns balance of IBA wei for given _user.
    function balanceOf (address _user) public view returns (uint256 balance) {
        return balances[_user];
    }

    // Sets allowance to execute transfer between current users
    // and _spender account for given _value.
    function approve (address _spender, uint256 _value)
        public returns (bool success)
    {
        allowed[msg.sender][_spender] = _value;
        emit Approval(msg.sender, _spender, _value);
        return true;
    }

    // Returns value of transfer allowance set between _owner and _spender.
    function allowance (address _owner, address _spender)
        public view returns (uint256 remaining)
    {
        return allowed[_owner][_spender];
    }
}


/**
Template copied from:
https://github.com/ConsenSys/Token-Factory/blob/master/contracts/HumanStandardToken.sol
*/

contract IbaBetaToken2 is StandardToken {

    using RealMath for *;

    // Public variables of the token.
    string public name;
    string public symbol;
    uint256 public decimals;
    uint256 public unit;

    uint256 public mainSupply;    // main IBA supply pool
    uint256 public promo1Supply;  // promotion level 1 IBA supply pool
    uint256 public promo2Supply;  // promotion level 2 IBA supply pool
    uint256 public prizeSupply;   // prize IBA supply pool
    uint256 public develSupply;   // development IBA supply pool
    uint256 public cooperSupply;  // cooperations IBA supply pool
    uint256 public soldSupply;    // sold IBA token pool

    // Checking current value of the Company Supply is possible
    // by using the following method.
    function companySupply () public view returns (uint256) {
        return balances[owner];
    }

    address private owner;        // owner of the contract

    // Supply identifiers.
    uint8 constant MAIN_SUPPLY = 1;
    uint8 constant COMPANY_SUPPLY = 2;
    uint8 constant PROMO1_SUPPLY = 3;
    uint8 constant PROMO2_SUPPLY = 4;
    uint8 constant PRIZE_SUPPLY = 5;
    uint8 constant DEVEL_SUPPLY = 6;
    uint8 constant COOPER_SUPPLY = 7;

    // Shortcut values for Real Math operations.
    int128 REAL_TEN = int88(10).toReal();
    int128 REAL_1_ETHER = REAL_TEN.ipow(18);

    // Emitted after successful deposit of Ether transfered into IBA tokens.
    event Deposit (
        address indexed _to,
        uint256 indexed _ibaValue,
        uint256 indexed _etherValue,
        uint256 _promo1,
        uint256 _promo2
    );

    event Withdraw (
        address indexed _to,
        uint256 indexed _etherValue
    );

    // Emitted after IBA tokens has been successfully transfered
    // by contract owner between the supply pools.
    event SupplyTransfer (
        uint8 indexed _fromSupplyId,
        uint8 indexed _toSupplyId,
        uint256 indexed _value
    );

    // Only the contract owner will be allowed to successfully execute
    // function marked by this modifier.
    modifier ownerOnly () {
        if (msg.sender != owner) {
            revert();
        }
        _;
    }

    // Returns true if _value of IBA wei can be withdrawn from the _supplyId.
    function _canTakeFromSupply (uint8 _supplyId, uint256 _value)
        private view returns (bool)
    {
        uint256 supply;

        if (_supplyId == MAIN_SUPPLY) {
            supply = mainSupply;
        } else if (_supplyId == COMPANY_SUPPLY) {
            supply = balances[owner];
        } else if (_supplyId == PROMO1_SUPPLY) {
            supply = promo1Supply;
        } else if (_supplyId == PROMO2_SUPPLY) {
            supply = promo2Supply;
        } else if (_supplyId == PRIZE_SUPPLY) {
            supply = prizeSupply;
        } else if (_supplyId == DEVEL_SUPPLY) {
            supply = develSupply;
        } else if (_supplyId == COOPER_SUPPLY) {
            supply = cooperSupply;
        } else {
            revert();
        }
        return supply >= _value;
    }

    // Withdraws _value of IBA wei from the _supplyId.
    // Returns true if succeeded.
    function _takeFromSupply (uint8 _supplyId, uint256 _value)
        private returns (bool)
    {
        if (!_canTakeFromSupply(_supplyId, _value)) {
            return false;
        }
        if (_supplyId == MAIN_SUPPLY) {
            mainSupply -= _value;
        } else if (_supplyId == COMPANY_SUPPLY) {
            balances[owner] -= _value;
        } else if (_supplyId == PROMO1_SUPPLY) {
            promo1Supply -= _value;
        } else if (_supplyId == PROMO2_SUPPLY) {
            promo2Supply -= _value;
        } else if (_supplyId == PRIZE_SUPPLY) {
            prizeSupply -= _value;
        } else if (_supplyId == DEVEL_SUPPLY) {
            develSupply -= _value;
        } else if (_supplyId == COOPER_SUPPLY) {
            cooperSupply -= _value;
        } else {
            // Unsupported supply id
            revert();
        }
        return true;
    }

    // Moves _value of IBA wei from _supplyId to the _to account.
    // Returns true if succeeded.
    function _giveFromSupply (address _to, uint8 _supplyId, uint256 _value)
        private returns (bool)
    {
        if (!_takeFromSupply(_supplyId, _value)) {
            return false;
        }
        if (_supplyId == MAIN_SUPPLY) {
            soldSupply += _value;
        }
        balances[_to] += _value;
        return true;
    }

    // Transfers _value of IBA wei between provided supply pools.
    // Returns true end emits SupplyTransfer event if succeeded.
    function supplyTransfer (
        uint8 _fromSupplyId, uint8 _toSupplyId, uint256 _value
    ) public ownerOnly returns (bool)
    {
        if (!_takeFromSupply(_fromSupplyId, _value)) {
            revert();
        }
        if (_toSupplyId == MAIN_SUPPLY) {
            mainSupply += _value;
        } else if (_toSupplyId == COMPANY_SUPPLY) {
            balances[owner] += _value;
        } else if (_toSupplyId == PROMO1_SUPPLY) {
            promo1Supply += _value;
        } else if (_toSupplyId == PROMO2_SUPPLY) {
            promo2Supply += _value;
        } else if (_toSupplyId == PRIZE_SUPPLY) {
            prizeSupply += _value;
        } else if (_toSupplyId == DEVEL_SUPPLY) {
            develSupply += _value;
        } else if (_toSupplyId == COOPER_SUPPLY) {
            cooperSupply += _value;
        } else {
            // Unsupported supply id
            revert();
        }
        emit SupplyTransfer(_fromSupplyId, _toSupplyId, _value);
        return true;
    }

    // Like supplyTransfer but _value is in IBA units.
    function supplyTransferUnits (
        uint8 _fromSupplyId, uint8 _toSupplyId, uint256 _value
    ) public ownerOnly returns (bool)
    {
        supplyTransfer(_fromSupplyId, _toSupplyId, _value * unit);
    }

    // Like balanceOf but returns balance in IBA units.
    function balanceOfUnits (address _user)
        public view returns (uint256 balance)
    {
        return balances[_user] / unit;
    }

    // Returns how many IBA wei can be currently bought for 1 Ether unit.
    // Performs Real Math calculations.
    function getBuyPrice () public view returns (int88) {
        int128 a; int128 b; int128 c; int128 d;

        /**
         * ibaWei = ( 1 * 10 ^18 ) / (
         *     ( 6666 / 10 ^7 ) *
         *     ( 1 000 000 015 / 10 ^9 ) ^( soldSupply / 10 ^18 )
         * )
         *
         * ibaWei = oneEther / (a * b)
         * a = 6666 / 10 ^7
         * b = c ^d
         * c = 1 000 000 015 / 10 ^9
         * d = soldSupply / 10 ^18
         */

        d = int88(soldSupply).toReal().div(REAL_TEN.ipow(18));
        c = int88(1000000015).toReal().div(REAL_TEN.ipow(9));
        b = c.ipow(int88(d.fromReal()));
        a = int88(6666).toReal().div(REAL_TEN.ipow(7));
        return REAL_1_ETHER.div(a.mul(b)).fromReal();
    }

    // Allows current user to send Ether
    // and transfer it into the the IBA tokens.
    function deposit () public payable {
        uint256 buyPrice = uint256(getBuyPrice());

        // ibaWei = buyPrice * depositedEtherWei / EtherUnit
        uint256 ibaWei = buyPrice * uint256(msg.value) / 1 ether;
        uint256 promo1Wei = ibaWei * 30 / 100;
        uint256 promo2Wei = ibaWei * 15 / 100;

        if (!_giveFromSupply(msg.sender, MAIN_SUPPLY, ibaWei)) {
            revert();
        }

        // Try to give additional promotion tokens if avalialbe in pool
        if (!_giveFromSupply(msg.sender, PROMO1_SUPPLY, promo1Wei)) {
            promo1Wei = 0;  // not enough promotion tokens in promo1 pool
            if (!_giveFromSupply(msg.sender, PROMO2_SUPPLY, promo2Wei)) {
                promo2Wei = 0;  // not enough promotion tokens in promo2 pool
            }
        }

        emit Deposit(msg.sender, ibaWei, msg.value, promo1Wei, promo2Wei);
    }

    // Launches deposit method if user sends Ether direcly to the contract.
    function () public payable {
        deposit();
    }

    // Returns current amount of Ether wei held by the contract.
    function contractEther () public view returns (uint256) {
        return address(this).balance;
    }

    // Like contractEther method but returns value in Ether units.
    function contractEtherUnits () public view returns (uint256) {
        return contractEther() / 1 ether;
    }

    // Withdraws all to the owner
    function withdraw() public {
        msg.sender.transfer(address(this).balance);
    }

    // Creates new IBA contract.
    constructor () public {
        name = 'IBA Beta2';
        symbol = 'IBAb2';
        decimals = 18;
        unit = 10 ** decimals;  // 1 IBA unit is that much IBA wei
        owner = msg.sender;     // owner of the contract

        totalSupply = 300 * 10 ** 6 * unit;  // 300 million IBA - hard cap
        mainSupply = totalSupply;
        soldSupply = 0;
        promo2Supply = 0;
        prizeSupply = 0;

        // Give 40% of the totalSupply to the contract owner.
        balances[owner] = 40 * totalSupply / 100;

        // Give 3% of the totalSupply to the PROMO1_SUPPLY.
        // At the end of PROMO 1 STAGE remaining funds will be manually
        // transferred from promo1Supply into the promo2Supply pool and finally
        // at the end of PROMO 2 STAGE into the prizeSupply.
        promo1Supply = 3 * totalSupply / 100;

        // Give 5% of the totalSupply to the DEVEL_SUPPLY
        develSupply = 5 * totalSupply / 100;

        // Give 3% of the totalSupply to the COOPER_SUPPLY
        cooperSupply = 3 * totalSupply / 100;

        // update mainSupply to reflect changes
        mainSupply -=
            balances[owner] + promo1Supply + develSupply + cooperSupply;
    }
}