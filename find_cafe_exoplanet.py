#!/usr/bin/env python3
"""
Find Exoplanet Near Optimal Café Location
Search real exoplanet catalog for planets near our chosen spot
"""

import json
import xml.etree.ElementTree as ET
from pathlib import Path
import math

def load_optimal_location():
    """Load the optimal café location we found"""
    with open("optimal_cafe_real_data.json") as f:
        data = json.load(f)
    return data["best_location"]

def angular_distance(ra1, dec1, ra2, dec2):
    """Calculate angular distance between two sky positions (degrees)"""
    # Convert to radians
    ra1_rad = math.radians(ra1)
    dec1_rad = math.radians(dec1)
    ra2_rad = math.radians(ra2)
    dec2_rad = math.radians(dec2)
    
    # Haversine formula
    dra = ra2_rad - ra1_rad
    ddec = dec2_rad - dec1_rad
    
    a = math.sin(ddec/2)**2 + math.cos(dec1_rad) * math.cos(dec2_rad) * math.sin(dra/2)**2
    c = 2 * math.asin(math.sqrt(a))
    
    return math.degrees(c)

def parse_exoplanet_xml(xml_file):
    """Parse exoplanet XML file"""
    try:
        tree = ET.parse(xml_file)
        root = tree.getroot()
        
        # Get system name
        name = root.find('name')
        system_name = name.text if name is not None else "Unknown"
        
        # Get coordinates (in HMS/DMS format)
        ra_elem = root.find('rightascension')
        dec_elem = root.find('declination')
        
        if ra_elem is None or dec_elem is None or not ra_elem.text or not dec_elem.text:
            return None
        
        # Convert HMS to decimal degrees
        ra_parts = ra_elem.text.split()
        if len(ra_parts) == 3:
            ra_deg = (float(ra_parts[0]) + float(ra_parts[1])/60 + float(ra_parts[2])/3600) * 15
        else:
            return None
        
        # Convert DMS to decimal degrees
        dec_text = dec_elem.text.replace('+', '').replace('-', ' -')
        dec_parts = dec_text.split()
        if len(dec_parts) == 3:
            sign = -1 if dec_parts[0].startswith('-') else 1
            dec_deg = sign * (abs(float(dec_parts[0])) + float(dec_parts[1])/60 + float(dec_parts[2])/3600)
        else:
            return None
        
        # Get distance
        distance = root.find('distance')
        dist_ly = None
        if distance is not None and distance.text:
            try:
                # Distance in parsecs, convert to light-years
                dist_pc = float(distance.text)
                dist_ly = dist_pc * 3.26156
            except:
                pass
        
        # Get planets
        planets = []
        for planet in root.findall('.//planet'):
            planet_name = planet.find('name')
            mass = planet.find('mass')
            radius = planet.find('radius')
            
            planets.append({
                "name": planet_name.text if planet_name is not None else "Unknown",
                "mass": mass.text if mass is not None else "Unknown",
                "radius": radius.text if radius is not None else "Unknown"
            })
        
        return {
            "system": system_name,
            "ra": ra_deg,
            "dec": dec_deg,
            "distance_ly": dist_ly,
            "planets": planets
        }
    except Exception as e:
        return None

def find_nearby_exoplanets():
    """Find exoplanets near optimal café location"""
    
    print("🪐 FINDING EXOPLANET NEAR CAFÉ LOCATION")
    print("=" * 70)
    print()
    
    # Load optimal location
    optimal = load_optimal_location()
    target_ra = optimal["ra"]
    target_dec = optimal["dec"]
    
    print(f"📍 Target location:")
    print(f"   RA:  {target_ra:.2f}°")
    print(f"   Dec: {target_dec:.2f}°")
    print()
    
    # Search exoplanet catalog
    print("🔍 Searching exoplanet catalog...")
    exo_dir = Path("astronomy_submodules/shard_00/open_exoplanet_catalogue/systems")
    
    if not exo_dir.exists():
        print(f"⚠️  Exoplanet directory not found: {exo_dir}")
        return
    
    xml_files = list(exo_dir.glob("*.xml"))
    print(f"   Found {len(xml_files)} exoplanet systems")
    print()
    
    # Find nearest exoplanets
    candidates = []
    
    for xml_file in xml_files[:500]:  # Sample first 500
        system = parse_exoplanet_xml(xml_file)
        if system and system["ra"] is not None and system["dec"] is not None:
            distance = angular_distance(target_ra, target_dec, system["ra"], system["dec"])
            system["angular_distance"] = distance
            candidates.append(system)
    
    # Sort by angular distance
    candidates.sort(key=lambda x: x["angular_distance"])
    
    # Show top 5 nearest
    print("🏆 TOP 5 NEAREST EXOPLANET SYSTEMS:")
    print()
    
    for i, sys in enumerate(candidates[:5], 1):
        print(f"{i}. {sys['system']}")
        print(f"   RA: {sys['ra']:.2f}°, Dec: {sys['dec']:.2f}°")
        print(f"   Angular distance: {sys['angular_distance']:.2f}°")
        if sys['distance_ly']:
            print(f"   Distance: {sys['distance_ly']:.1f} light-years")
        print(f"   Planets: {len(sys['planets'])}")
        for planet in sys['planets']:
            print(f"     • {planet['name']}")
        print()
    
    # Best candidate
    if candidates:
        best = candidates[0]
        
        print("=" * 70)
        print("✅ EXOPLANET FOUND FOR CAFÉ!")
        print()
        print(f"🪐 System: {best['system']}")
        print(f"   RA:  {best['ra']:.2f}°")
        print(f"   Dec: {best['dec']:.2f}°")
        print(f"   Angular distance from café: {best['angular_distance']:.2f}°")
        if best['distance_ly']:
            print(f"   Distance: {best['distance_ly']:.1f} light-years")
        print()
        print(f"   Planets ({len(best['planets'])}):")
        for planet in best['planets']:
            print(f"     • {planet['name']}")
            if planet['mass'] != "Unknown":
                print(f"       Mass: {planet['mass']} Jupiter masses")
            if planet['radius'] != "Unknown":
                print(f"       Radius: {planet['radius']} Jupiter radii")
        print()
        print("☕ Perfect spot for Milliways with a view of exoplanets!")
        print()
        print("☕🕳️🪟👁️👹🦅🐓🌌🪐")
        
        # Save results
        with open("cafe_exoplanet.json", "w") as f:
            json.dump({
                "cafe_location": optimal,
                "nearest_exoplanet": best,
                "top_5": candidates[:5]
            }, f, indent=2)
        
        print()
        print("💾 Results saved to: cafe_exoplanet.json")

if __name__ == "__main__":
    find_nearby_exoplanets()
