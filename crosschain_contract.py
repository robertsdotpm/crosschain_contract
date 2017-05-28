"""
This is old contract code that I wrote for cross-chain contracts. The code depends on some config stuff and assumes a server to fix a DoS attack where an attacker tricks a trader into depositing coins and wastes their time having to wait for a refund when they don't have to go through with it themselves. A server isn't actually needed for this contract and doesn't reduce trust by introducing it. It can be removed if you don't care about DoS attacks - its just something I was experimenting with at the time.

FYI: Don't use this code. It's provided here for example use only.
Bonus section: Peter Todd kindly helped me debug an issue with the Python-bitcoinlib library back in the day. That was years ago now but thanks for that - it was driving me insane.
"""


import binascii
import bitcoin
import decimal

from bitcoin import SelectParams
from bitcoin.core import b2x, lx, x, COIN, COutPoint, CTxOut, CTxIn, CTransaction, Hash160, Serializable
from bitcoin.core.script import CScript, OP_DUP, OP_NUMEQUAL, OP_DROP, OP_HASH160, OP_EQUALVERIFY, OP_CHECKSIG, SignatureHash, SIGHASH_ALL, SIGHASH_ANYONECANPAY, SIGHASH_SINGLE, OP_IF, OP_CHECKMULTISIGVERIFY, OP_NOTIF, OP_ELSE, OP_ENDIF, OP_VERIFY, OP_SHA256, OP_CHECKSIGVERIFY, OP_EQUAL, OP_FALSE, OP_3, OP_0, OP_1, OP_2, OP_5, OP_4, OP_TOALTSTACK, OP_TRUE, OP_DEPTH
from bitcoin.core.scripteval import VerifyScript, SCRIPT_VERIFY_P2SH
from bitcoin.wallet import CBitcoinAddress, CBitcoinSecret

from bitcoinrpc.authproxy import AuthServiceProxy
import hashlib
import random
import datetime
import coinbend

class CrosschainContract():
    """
    Todo:
    Multi-threaded.
    Mutexes
    With timeout
    """
    def analyze_key_pair(self, key_pair):
        #pub = binascii.unhexlify(key_pair["pub"])
        pub = CBitcoinSecret(key_pair["priv"]).pub
        
        return {
            "addr": {
                "base58": key_pair["addr"]
            },
            "pub": {
                "hex": key_pair["pub"],
                "bin": pub
            },
            "priv": {
                "wif": key_pair["priv"],
                "hex": None,
                "bin": None
            }
        }
         
    def set_transaction(self, name, tx_hex):
        self.transactions[name]["hex"] = tx_hex
        if tx_hex == None:
            self.transactions[name]["CTransaction"] = None
            self.transactions[name]["txid_hex"] = None
        else:
            self.transactions[name]["CTransaction"] = CTransaction.deserialize(
            binascii.unhexlify(self.transactions[name]["hex"]))
            self.transactions[name]["txid_hex"] = self.calculate_txid(
            self.transactions[name]["hex"])
        self.transactions[name]["is_broadcast"] = 0
        self.transactions[name]["confirmations"] = 0
        self.transactions[name]["malleability_occured"] = 0
    
    def __init__(self, match_id, pair, send_amount, recv_amount, buyer_key_pair, seller_key_pair, secret_info, action):
        #Config.
        self.minimum_confirmations = 1
        self.minimum_blocks = 10
        self.future_minutes = 30
        
        #Calculate maximum time required to complete contract (once started.)
        """
        In reality, max_resolution_time will factor in average block rate,
        difficulty, future bounce time, etc, for individual currencies in
        order to produce a more accurate estimate of a contract's total time.
        """
        self.max_resolution_time = 60 * 60 * 2 #2 hours.
        
        #Setup blockchain.
        SelectParams(coinbend.config["blockchain"])
        
        #Setup key pairs and convert to binary.
        self.key_pairs = {}
        i = 1
        for arbiter_key_pair in coinbend.config["arbiter_key_pairs"]:
            name = "arbiter_" + str(i)
            self.key_pairs[name] = self.analyze_key_pair(arbiter_key_pair)
            i += 1            
        self.key_pairs["buyer"] = self.analyze_key_pair(buyer_key_pair)
        self.key_pairs["seller"] = self.analyze_key_pair(seller_key_pair)
        
        #Type checks.
        if type(send_amount) != decimal.Decimal:
            raise Exception("Send amount must be type decimal.")
        if type(recv_amount) != decimal.Decimal:
            raise Exception("Recv amount must be type decimal.")
        
        self.send_amount = send_amount
        self.recv_amount = recv_amount
        self.pair = pair
        self.action = action
        self.my = self.action + "er"
        self.their = "buyer"
        if self.my == "buyer":
            self.their = "seller"
        self.secret_info = secret_info
        self.match_id = match_id
        
        """
        See set_transaction function for what this
        data structure looks like. Here is a brief idea:
        is_broadcast (int)
        confirmations (int)
        txid_hex (str)
        malleability_occured (int)
        sigs {their / my: signature for tx}
        hex (str) - tx binary in hex string format
        CTransaction (CTransaction) - deserialized transaction
        """
        self.transactions = {
            "fund": {},
            "bounce": {},
            "claim": {},
            "arbitrate": {}
        }
        
        #Set to the TX ids once they are sent.
        self.status = {
            "fund": None,
            "bounce": None,
            "claim": None,
            "arbitrate": None,
        }

        #Setup *coind JSON-RPC connections.
        self.jsonrpc = {}
        i = 0
        for currency in self.pair:
            jsonrpc_config = coinbend.config["jsonrpc_servers"][currency]
            end_point = "http://%s:%s@%s:%s" % (
            jsonrpc_config["user"],
            jsonrpc_config["pass"],
            jsonrpc_config["addr"],
            jsonrpc_config["port"])
            name = "buyer"
            if i == 0:
                name = "seller"
            self.jsonrpc[name] = self.jsonrpc[currency] = AuthServiceProxy(end_point)
            i += 1
            
        #Record timestamp creation.
        self.created_at = int(datetime.datetime.now().strftime("%s"))
        
        """
        Record best 10 blocks at the top of the longest chain for
        block crypto currencies being traded. This provides
        orphan protection. Blocks are in order from least recent
        to most recent.
        """
        self.blockchains = {}
        for currency in self.pair:
            blockchain = []
            best_block_hash = self.jsonrpc[currency].getbestblockhash()
            best_block = self.jsonrpc[currency].getblock(best_block_hash)
            blockchain.insert(0, best_block_hash)
            current_block_hash = best_block["previousblockhash"]
            for i in range(1, self.minimum_blocks):
                current_block = self.jsonrpc[currency].getblock(current_block_hash)
                blockchain.insert(0, current_block_hash)
                current_block_hash = current_block["previousblockhash"]
            self.blockchains[currency] = blockchain
            
        #Record redeem scripts.
        self.fund_redeem_scripts = {
            self.my: self.fund_redeem_script(self.my),
            self.their: self.fund_redeem_script(self.their)
        }
        
        #Build fund transaction.
        tx_hex = self.build_fund_tx(self.fund_redeem_scripts[self.my])
        self.set_transaction("fund", tx_hex)
        sighash = SignatureHash(
            self.fund_redeem_scripts[self.my]["bin"],
            self.transactions["fund"]["CTransaction"],
            0,
            SIGHASH_ALL
        )
        self.transactions["fund"]["sighash"] = {}
        self.transactions["fund"]["sighash"]["bin"] = sighash
        self.transactions["fund"]["sighash"]["hex"] = str(binascii.hexlify(sighash))[2:-1]
        
        #Build bounce transaction.
        tx_hex = self.build_bounce_tx(self.transactions["fund"]["txid_hex"])
        self.set_transaction("bounce", tx_hex)
        self.transactions["bounce"]["sigs"] = {
            #Calculate our signature for our bounce tx.
            self.my: self.sign_bounce_tx(self.transactions["fund"]["sighash"]["hex"]),
            #Their signature is still required before we broadcast our fund tx.
            self.their: None
        }
        
        """
        Build claim transaction.
        
        We can't know this at contract creation until we know the txid_hex
        for their fund transaction. This sets the data structures up with
        blank information for the transaction part.
        """
        self.set_transaction("claim", None)
        
            
    def key_pair_from_address(self, address, person):
        key_pair = {
            "addr": address,
            "pub": "",
            "priv": ""
        }
        key_pair["pub"] = self.jsonrpc[person].validateaddress(address)["pubkey"]
        key_pair["priv"] = self.jsonrpc[person].dumpprivkey(address)
        key_pair = self.analyze_key_pair(key_pair)
        return key_pair
        
    def script_to_address(self, script, person):
        try:
            #Programming is the art of laziness.
            address = str(self.jsonrpc[person].decodescript(script["hex"])["p2sh"])
        except:
            raise Exception("Unable to generate p2sh address.")
        return address
        
    def hash160_script(self, script):
        bin_hash = Hash160(script["bin"])
        return {
            "hex": binascii.hexlify(bin_hash).decode("ascii"),
            "bin": bin_hash
        }
        
    def reverse_hex(self, hex_str):
        hex_str_len = len(hex_str)
        backwards_man = ""        
        
        #Check if bytes are in correct hex format.
        if hex_str_len % 2:
            raise Exception("Unable to reverse hex_str")
            
        #Reverse hex bytes.
        for i in list(reversed(range(1, int(hex_str_len / 2) + 1))):
            byte_me = hex_str[(i * 2) - 2:i * 2]
            backwards_man += byte_me
        
        #Returns a hex string with correct txid.    
        return backwards_man
        
    def calculate_txid(self, tx_hex):
        #Txid is double sha256 hash of serialized transaction.
        single = binascii.unhexlify(hashlib.sha256(binascii.unhexlify(tx_hex)).hexdigest())
        double = hashlib.sha256(single).hexdigest()
        return self.reverse_hex(double) #Litte endian.
        
    def fund_redeem_script(self, person):
        """
        Notes:
        * Release pub key changes depending on contract side and whether they are the buyer or seller.
        """
        #Function can be used to create fund script for either buyer or seller.
        my = person
        their = "buyer"
        if my == their:
            their = "seller"
        
        #Begin Bitcoin Script asm code.  
        script = CScript([
            OP_DUP,
            1,
            OP_NUMEQUAL,
            OP_IF, #Possible input for my bounce.
                OP_DROP,
                2,
                self.key_pairs["seller"]["pub"]["bin"],
                self.key_pairs["buyer"]["pub"]["bin"],
                2,
                OP_CHECKMULTISIGVERIFY,
            OP_ELSE, #Possible input for my refund.
                2,
                OP_NUMEQUAL,
                OP_IF,
                    5,
                    self.key_pairs[my]["pub"]["bin"],
                    self.key_pairs["arbiter_1"]["pub"]["bin"],
                    self.key_pairs["arbiter_2"]["pub"]["bin"],
                    self.key_pairs["arbiter_3"]["pub"]["bin"],
                    self.key_pairs["arbiter_4"]["pub"]["bin"],
                    5,
                    OP_CHECKMULTISIGVERIFY,
                OP_ELSE, #Possible input for their claim.
                    self.key_pairs[their]["pub"]["bin"],
                    OP_CHECKSIGVERIFY,
                    OP_SHA256,
                    self.secret_info["hash"]["bin"],
                    OP_EQUALVERIFY,
                OP_ENDIF,
            OP_ENDIF,
            1,
            OP_DEPTH,
            1,
            OP_NUMEQUAL,
            OP_IF,
                OP_TRUE,
            OP_ELSE,
                OP_FALSE,
            OP_ENDIF])
            
        return {
            "bin": script,
            "hex": binascii.hexlify(script).decode("ascii")
        }
        
    def build_fund_tx(self, redeem_script):
        if type(self.send_amount) != decimal.Decimal:
            raise Exception("Please only use decimal types for the amount.")
        if self.send_amount < decimal.Decimal(coinbend.config["minimum_trade"]):
            raise Exception("Amount is too small.")
        
        #Because every Satoshi counts.
        decimal.getcontext().prec = 50
        
        #Create a change address.
        if "change" not in self.key_pairs:
            self.key_pairs["change"] = self.key_pair_from_address(self.jsonrpc[self.my].getnewaddress(), self.my)
            
        #Get wallet balance.
        balance = self.jsonrpc[self.my].getbalance()
        
        #Check we have enough.
        if balance < self.send_amount:
            raise Exception("Insufficent balance to cover fund.")    
            
        #List unclaimed outputs.
        unspent_outputs = self.jsonrpc[self.my].listunspent()
        
        #Setup tx inputs.
        change_amount = decimal.Decimal("0")
        txins = []
        total = decimal.Decimal("0")
        indexes = []
        i = 0
        for unspent_output in unspent_outputs:
            #Skip outputs that don't satisfy min confirmations.
            if unspent_output["confirmations"] < self.minimum_confirmations:
                i += 1
                continue
                
            #Check scriptPubKey is pay to pub key hash.
            if self.jsonrpc[self.my].decodescript(unspent_output["scriptPubKey"])["type"] != "pubkeyhash":
                i += 1
                continue
             
            #Record key pairs.
            if unspent_output["address"] not in self.key_pairs:
                self.key_pairs[unspent_output["address"]] = self.key_pair_from_address(unspent_output["address"], self.my)
            
            #Build new txin.
            txid = lx(unspent_output["txid"])
            vout = unspent_output["vout"]
            txin = CTxIn(COutPoint(txid, vout))
            txins.append(txin)
            indexes.append(i)
            total += unspent_output["amount"]
            i += 1
                
            if total > self.send_amount:
                break
                
            if total == self.send_amount:
                break
        
        #Insufficent funds.
        if total < self.send_amount:
            raise Exception("Not enough valid inputs to fund contract.")
        
        #Calculate change.        
        change = total - self.send_amount
        
        #Build txouts.
        txouts = []
        redeem_script_hash160 = self.hash160_script(redeem_script)
        p2sh_script_pub_key = CScript([OP_HASH160, redeem_script_hash160["bin"], OP_EQUAL])
        txouts.append(CTxOut((self.send_amount - decimal.Decimal(coinbend.config["mining_fee"]["standard"])) * COIN, p2sh_script_pub_key))
        if change > decimal.Decimal("0"):
            change_seckey = CBitcoinSecret(self.key_pairs["change"]["priv"]["wif"])
            change_script_pub_key = CScript([OP_DUP, OP_HASH160, Hash160(change_seckey.pub), OP_EQUALVERIFY, OP_CHECKSIG])
            txouts.append(CTxOut(change * COIN, change_script_pub_key))
            
        #Build unsigned transaction.
        tx = CTransaction(txins, txouts)
        unsigned_tx_hex = b2x(tx.serialize())
        
        #Sign transaction.
        signed_tx_hex = self.jsonrpc[self.my].signrawtransaction(unsigned_tx_hex)["hex"]
        return signed_tx_hex
        
    def build_claim_tx(self, txid_hex):
        if self.secret_info["plaintext"] == None:
            raise Exception("We don't know the secret yet.")
                    
        #Create redeem script.    
        redeem_script = self.fund_redeem_script(self.their)
        
        #Convert to p2sh address.
        their_fund_address = self.script_to_address(redeem_script, self.their)
        
        #Check there is enough in the p2sh address.
        their_fund_tx = self.jsonrpc[self.their].gettransaction(txid_hex)["details"]
        found = 0
        for tx_input in their_fund_tx:
            #Check it's the right input.
            if tx_input["address"] == their_fund_address:
                found = 1
                if tx_input["amount"] + self.recv_amount > decimal.Decimal(coinbend.config["mining_fee"]["standard"]):
                    raise Exception("Their contract has not been sufficently funded.")
                break
            else:
                continue
                
        #Their side of the contract hasn't been funded.
        if not found:
            raise Exception("Their contract fund output was not detected.")

        #Generate address to receive redeemed output.
        if "receive" not in self.key_pairs:
            self.key_pairs["receive"] = self.key_pair_from_address(self.jsonrpc[self.their].getnewaddress(), self.their)
        
        #Load private key for signing.
        seckey = CBitcoinSecret(self.key_pairs[self.my]["priv"]["wif"])
        
        #Generate p2sh script pub key.
        redeem_script_hash160 = self.hash160_script(redeem_script)
        txin_script_pub_key = CScript([OP_HASH160, redeem_script_hash160["bin"], OP_EQUAL])

        #Setup tx inputs and outputs.
        txid = lx(txid_hex)
        vout = 0
        txin = CTxIn(COutPoint(txid, vout))
        txout = CTxOut((self.recv_amount - decimal.Decimal(coinbend.config["mining_fee"]["standard"])) * COIN, CBitcoinAddress(self.key_pairs["receive"]["addr"]["base58"]).to_scriptPubKey())

        #Create unsigned transaction.
        tx = CTransaction([txin],[txout])

        #Sign transactions.
        sighash = SignatureHash(redeem_script["bin"], tx, 0, SIGHASH_ALL)
        sig = seckey.sign(sighash) + bytes([SIGHASH_ALL])
        txin.scriptSig = CScript([bytes(self.secret_info["plaintext"].encode("ascii")), sig, OP_3, redeem_script["bin"]])

        #Return signed transaction hex.
        return b2x(tx.serialize())
        
    def sign_bounce_tx(self, sighash_hex):
        sighash = binascii.unhexlify(sighash_hex)
        seckey = CBitcoinSecret(self.key_pairs[self.my]["priv"]["wif"])
        sig = seckey.sign(sighash) + bytes([SIGHASH_ALL])
        return sig
        
    def build_bounce_tx(self, txid_hex):
        #Generate p2sh script pub key.
        redeem_script = self.fund_redeem_script(self.my)
        redeem_script_hash160 = self.hash160_script(redeem_script)
        txin_script_pub_key = CScript([OP_HASH160, redeem_script_hash160["bin"], OP_EQUAL])
        
        #Generate address to receive bounce.
        if "bounce" not in self.key_pairs:
            self.key_pairs["bounce"] = self.key_pair_from_address(self.jsonrpc[self.my].getnewaddress(), self.my)

        #Setup tx inputs and outputs.
        txid = lx(txid_hex)
        vout = 0
        txin = CTxIn(COutPoint(txid, vout), CScript(), 0) #Sequence number 0.
        txout = CTxOut((self.send_amount - decimal.Decimal(coinbend.config["mining_fee"]["standard"])) * COIN, CBitcoinAddress(self.key_pairs["bounce"]["addr"]["base58"]).to_scriptPubKey())

        #Locktime is unsigned int 4, unix timestamp in little endian format.
        #(Conversion to little endian is handled by the library already.)
        nlock_time = datetime.datetime.now() + datetime.timedelta(seconds=self.future_minutes * 60)
        nlock_time = int(nlock_time.strftime("%s"))

        #Create unsigned transaction.
        tx = CTransaction([txin], [txout], nlock_time)
        return b2x(tx.serialize())
        
        
    def record_contract(self):
        pass


buyer_key_pair = {
    "addr": "mhCMwU6Him3qV9dUBjA7BuBqi9KYhUVghU",
    "pub": "03ad6bb76e00d124f07a22680e39debd4dc4bdb1aa4b893720dd05af3c50560fdd",
    "priv": "cSWRm52RLqaBbqniEobrd2uKrPfkCgrL7amZ41X7Lz68DZbz7Cht"
}

seller_key_pair = {
    "addr": "mvTxpqy5vMEbdvnD9WLaEPhB4PixpE9ij2",
    "pub": "03b124c48bbff7ebe16e7bd2b2f2b561aa53791da678a73d2777cc1ca4619ab6f7",
    "priv": "cUyhzgqW6UX1EuLGFSwiTHTcNL5r9CnwKSR4QBQCW2UNDU1xgBoi"
}

secret = "A cat is fine too."
secret_hash_hex = str(hashlib.sha256(secret.encode("ascii")).hexdigest())
secret_hash_bin = binascii.unhexlify(secret_hash_hex)
secret_info = {
    "plaintext": secret,
    "hash": {
        "hex": secret_hash_hex,
        "bin": secret_hash_bin
    }
}



send_amount = decimal.Decimal("0.006")
recv_amount = decimal.Decimal("0.003")
seller_contract = CrosschainContract(
match_id=None,
pair=["btc", "ltc"],
send_amount=send_amount,
recv_amount=recv_amount,
buyer_key_pair=buyer_key_pair,
seller_key_pair=seller_key_pair,
secret_info=secret_info,
action="sell")
print(seller_contract.transactions["fund"]["hex"])
exit()


#redeem_script = seller_contract.fund_redeem_script(seller_contract.my)
#seller_fund_tx = seller_contract.build_fund_tx(redeem_script)
#seller_fund_txid = seller_contract.calculate_txid(seller_fund_tx)

"""


txid_hex = "c926caf4302c298029ad190fc97a5bb8750f7544596e1449fdb3d3afe76c85dc"

unsigned_bounce_tx = seller_contract.build_bounce_tx(txid_hex)
    
    
seller_fund_txid = "8d6ae095f9c7c4af52a7d9ed7896fd7851ea46bd0cc31acd8a3a03aed940c045"
secret_info["plaintext"] = None #We don't know it yet.
buyer_contract = CrosschainContract(
match_id=None,
pair=["btc", "ltc"],
send_amount=decimal.Decimal("0.002"),
recv_amount=decimal.Decimal("0.004"),
buyer_key_pair=buyer_key_pair,
seller_key_pair=seller_key_pair,
secret_info=secret_info,
action="buy")
buyer_redeem_script = buyer_contract.fund_redeem_script(buyer_contract.their)
#Simulate secret release.
buyer_contract.secret_info["plaintext"] = "I liek cats."
buyer_claim_tx = buyer_contract.build_claim_tx(seller_fund_txid)
buyer_claim_txid = buyer_contract.calculate_txid(buyer_claim_tx)



tx = CTransaction.deserialize(binascii.unhexlify(unsigned_bounce_tx))
sighash = SignatureHash(redeem_script["bin"], tx, 0, SIGHASH_ALL)
sighash_hex = str(binascii.hexlify(sighash))[2:-1]
seller_sig = seller_contract.sign_bounce_tx(sighash_hex)
buyer_sig = buyer_contract.sign_bounce_tx(sighash_hex)
tx.vin[0].scriptSig = CScript([OP_2, seller_sig, buyer_sig, OP_1, redeem_script["bin"]])



#Return it.
tx_hex = b2x(tx.serialize())
print(tx_hex)
"""
