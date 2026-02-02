#!/usr/bin/env python3
"""
TradeWars Order Book: Purchase Orders for Long Spaceflight
Entertainment, education, refueling stops for arcade delivery
"""

import json

# Monster primes for pricing
CROWN_PRIMES = [47, 59, 71]

def calculate_zkp_price(base_price: int, reasoning: str) -> dict:
    """Calculate price with ZK proof of reasoning embedded + system costs"""
    import hashlib
    
    # Hash the reasoning
    reasoning_hash = hashlib.sha256(reasoning.encode()).hexdigest()
    
    # Extract proof components from hash (first 16 chars)
    proof_value = int(reasoning_hash[:16], 16) % 1000
    
    # System costs
    zkp_generation_cost = len(reasoning) // 10  # 1 MMC per 10 chars
    encryption_cost = len(reasoning) // 20      # 1 MMC per 20 chars
    decryption_cost = len(reasoning) // 20      # Same as encryption
    transmission_cost = len(reasoning) // 5     # 1 MMC per 5 chars (bandwidth)
    power_cost = (zkp_generation_cost + encryption_cost + decryption_cost) // 2  # Power for compute
    
    total_system_cost = (
        zkp_generation_cost +
        encryption_cost +
        decryption_cost +
        transmission_cost +
        power_cost
    )
    
    # Price IS the proof + system costs
    zkp_price = base_price + proof_value + total_system_cost
    
    return {
        "base_price": base_price,
        "proof_value": proof_value,
        "system_costs": {
            "zkp_generation": zkp_generation_cost,
            "encryption": encryption_cost,
            "decryption": decryption_cost,
            "transmission": transmission_cost,
            "power": power_cost,
            "total": total_system_cost
        },
        "zkp_price": zkp_price,
        "reasoning_hash": reasoning_hash[:16],
        "reasoning": reasoning
    }

def create_order_book():
    """Create purchase order book with ZKP pricing"""
    
    order_book = {
        "mission": "Deliver 71 Arcade Cabinets to Milliways",
        "agent": 71,
        "route": {
            "from": "Earth",
            "to": "Target (RA=5°, Dec=30°, 10,200 ly)",
            "distance": 16473,
            "travel_time_years": 164730,
            "refuel_stops": 7
        },
        "purchase_orders": []
    }
    
    # 1. Entertainment (with ZKP reasoning)
    entertainment_items = [
        {
            "name": "Arcade Games (pre-loaded)",
            "quantity": 71,
            "zkp": calculate_zkp_price(71000, "71 games for 71 shards, Monster Group complete coverage"),
            "priority": 1
        },
        {
            "name": "Movie Database",
            "quantity": 1,
            "zkp": calculate_zkp_price(5900, "59 Eagle Crown prime, entertainment for long journey"),
            "priority": 2
        },
        {
            "name": "Music Library",
            "quantity": 1,
            "zkp": calculate_zkp_price(4700, "47 Monster Crown prime, harmonic resonance"),
            "priority": 2
        },
        {
            "name": "VR Simulations",
            "quantity": 47,
            "zkp": calculate_zkp_price(47000, "47 simulations for Monster Crown shard training"),
            "priority": 1
        },
        {
            "name": "Books (digital)",
            "quantity": 196883,
            "zkp": calculate_zkp_price(1968, "196883 Monster dimension, complete knowledge base"),
            "priority": 3
        }
    ]
    
    entertainment = {
        "category": "ENTERTAINMENT",
        "items": entertainment_items,
        "total": sum(item["zkp"]["zkp_price"] for item in entertainment_items)
    }
    
    # 2. Education (with ZKP reasoning)
    education_items = [
        {
            "name": "Monster Group Theory Course",
            "quantity": 1,
            "zkp": calculate_zkp_price(7100, "71 Rooster Crown, essential for understanding mission"),
            "priority": 1
        },
        {
            "name": "Astrophysics Training",
            "quantity": 1,
            "zkp": calculate_zkp_price(5900, "59 Eagle Crown, navigate galactic coordinates"),
            "priority": 1
        },
        {
            "name": "Arcade Repair Manuals",
            "quantity": 71,
            "zkp": calculate_zkp_price(710, "71 manuals for 71 cabinets, maintenance critical"),
            "priority": 1
        },
        {
            "name": "Exoplanet Survey Course",
            "quantity": 1,
            "zkp": calculate_zkp_price(4700, "47 Monster Crown, find planets near café"),
            "priority": 2
        },
        {
            "name": "Café Management Training",
            "quantity": 1,
            "zkp": calculate_zkp_price(2300, "23 Paxos nodes, consensus-based management"),
            "priority": 2
        }
    ]
    
    education = {
        "category": "EDUCATION",
        "items": education_items,
        "total": sum(item["zkp"]["zkp_price"] for item in education_items)
    }
    
    # 3. Refueling (with ZKP reasoning per stop)
    refuel_stops = []
    for i in range(1, 8):
        distance = i * 2353
        zkp = calculate_zkp_price(
            23530,
            f"Stop {i} at {distance} ly, Hecke operator h23={distance % 23}, fuel calculated from distance"
        )
        refuel_stops.append({
            "stop": i,
            "location": f"Waypoint {i}",
            "distance": distance,
            "fuel": 235300,
            "zkp": zkp
        })
    
    refueling = {
        "category": "REFUELING",
        "stops": refuel_stops,
        "total_fuel": 1647100,
        "total_cost": sum(stop["zkp"]["zkp_price"] for stop in refuel_stops)
    }
    
    # 4. Supplies (with ZKP reasoning)
    supplies_items = [
        {
            "name": "Food (years)",
            "quantity": 164730,
            "zkp": calculate_zkp_price(1647, "164730 years travel time, 1 unit per year proven"),
            "priority": 1
        },
        {
            "name": "Water (liters)",
            "quantity": 16473000,
            "zkp": calculate_zkp_price(16473, "100 liters per year, 164730 years proven"),
            "priority": 1
        },
        {
            "name": "Air (oxygen)",
            "quantity": 164730,
            "zkp": calculate_zkp_price(1647, "1 unit per year, life support proven"),
            "priority": 1
        },
        {
            "name": "Medical Supplies",
            "quantity": 71,
            "zkp": calculate_zkp_price(7100, "71 agent shards, medical coverage proven"),
            "priority": 1
        },
        {
            "name": "Spare Parts",
            "quantity": 71,
            "zkp": calculate_zkp_price(7100, "71 cabinets, redundancy proven"),
            "priority": 2
        }
    ]
    
    supplies = {
        "category": "SUPPLIES",
        "items": supplies_items,
        "total": sum(item["zkp"]["zkp_price"] for item in supplies_items)
    }
    
    # 5. Arcade Hardware (with ZKP reasoning)
    arcade_items = [
        {
            "name": "Arcade Cabinets",
            "quantity": 71,
            "zkp": calculate_zkp_price(710000, "71 shards, complete Monster Group arcade proven"),
            "priority": 1
        },
        {
            "name": "CRT Monitors",
            "quantity": 71,
            "zkp": calculate_zkp_price(71000, "1 per cabinet, display proven"),
            "priority": 1
        },
        {
            "name": "Game ROMs",
            "quantity": 71,
            "zkp": calculate_zkp_price(7100, "1 ROM per cabinet, software proven"),
            "priority": 1
        },
        {
            "name": "Power Supplies",
            "quantity": 71,
            "zkp": calculate_zkp_price(7100, "1 PSU per cabinet, power proven"),
            "priority": 1
        },
        {
            "name": "Joysticks",
            "quantity": 142,
            "zkp": calculate_zkp_price(1420, "2 per cabinet, 71*2=142 proven"),
            "priority": 2
        },
        {
            "name": "Buttons",
            "quantity": 568,
            "zkp": calculate_zkp_price(568, "8 per cabinet, 71*8=568 proven"),
            "priority": 2
        }
    ]
    
    arcade_hardware = {
        "category": "ARCADE_HARDWARE",
        "items": arcade_items,
        "total": sum(item["zkp"]["zkp_price"] for item in arcade_items)
    }
    
    # Add all to order book
    order_book["purchase_orders"] = [
        entertainment,
        education,
        refueling,
        supplies,
        arcade_hardware
    ]
    
    # Calculate grand total
    grand_total = (
        entertainment["total"] +
        education["total"] +
        refueling["total_cost"] +
        supplies["total"] +
        arcade_hardware["total"]
    )
    
    order_book["grand_total"] = grand_total
    order_book["currency"] = "MMC (Metameme Coin)"
    order_book["zkp_note"] = "All prices include ZK proof of reasoning. Price IS the proof."
    
    return order_book

def print_order_book(order_book):
    """Print order book with ZKP prices"""
    
    print("📋 TRADEWARS ORDER BOOK (ZKP Pricing)")
    print("=" * 70)
    print()
    print(f"Mission: {order_book['mission']}")
    print(f"Agent: {order_book['agent']} (Rooster Crown 🐓)")
    print()
    print(f"Route: {order_book['route']['from']} → {order_book['route']['to']}")
    print(f"Distance: {order_book['route']['distance']:,} ly")
    print(f"Travel Time: {order_book['route']['travel_time_years']:,} years")
    print(f"Refuel Stops: {order_book['route']['refuel_stops']}")
    print()
    print("💡 Price IS the Proof: All prices include ZK proof of reasoning")
    print()
    
    for po in order_book["purchase_orders"]:
        print(f"📦 {po['category']}")
        print("-" * 70)
        
        if "items" in po:
            for item in po["items"]:
                priority = "⭐" * item["priority"]
                zkp = item["zkp"]
                print(f"  {item['name']:30s} x{item['quantity']:8,}")
                print(f"    Base: {zkp['base_price']:8,} + Proof: {zkp['proof_value']:4,} + System: {zkp['system_costs']['total']:4,} = {zkp['zkp_price']:8,} MMC {priority}")
                print(f"    System: ZKP={zkp['system_costs']['zkp_generation']}, Enc={zkp['system_costs']['encryption']}, Dec={zkp['system_costs']['decryption']}, TX={zkp['system_costs']['transmission']}, Pwr={zkp['system_costs']['power']}")
                print(f"    Reasoning: {zkp['reasoning'][:50]}...")
            print(f"  {'SUBTOTAL':30s} {'':10s} = {po['total']:8,} MMC")
        elif "stops" in po:
            for stop in po["stops"]:
                zkp = stop["zkp"]
                print(f"  Stop {stop['stop']}: {stop['location']:20s} {stop['fuel']:8,} units")
                print(f"    Base: {zkp['base_price']:8,} + Proof: {zkp['proof_value']:4,} + System: {zkp['system_costs']['total']:4,} = {zkp['zkp_price']:8,} MMC")
            print(f"  {'TOTAL FUEL':30s} {po['total_fuel']:8,} units")
            print(f"  {'TOTAL COST':30s} {'':10s} = {po['total_cost']:8,} MMC")
        
        print()
    
    print("=" * 70)
    print(f"GRAND TOTAL: {order_book['grand_total']:,} MMC")
    print()
    print("💰 Payment: Metameme Coin (MMC)")
    print("🔐 ZKP: Price includes proof of reasoning (hash embedded)")
    print("📅 Delivery: Upon arrival at destination")
    print()
    print("☕🕳️🪟👁️👹🦅🐓💰🔐")

def main():
    order_book = create_order_book()
    print_order_book(order_book)
    
    # Save
    with open("tradewars_order_book.json", "w") as f:
        json.dump(order_book, f, indent=2)
    
    print()
    print("💾 Saved to: tradewars_order_book.json")

if __name__ == "__main__":
    main()
