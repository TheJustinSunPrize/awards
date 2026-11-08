import os
import re
import unittest

class TestCatalogBounties(unittest.TestCase):
    def test_jsp_000118_historical_bounty(self):
        catalog_path = os.path.join("problems", "catalog-0101-0200.md")
        self.assertTrue(os.path.exists(catalog_path), f"Catalog file {catalog_path} does not exist.")
        
        with open(catalog_path, "r", encoding="utf-8") as f:
            content = f.read()
            
        jsp_section_match = re.search(r"##\s+JSP-000118[\s\S]*?(?=##\s+JSP-|\Z)", content)
        self.assertIsNotNone(jsp_section_match, "JSP-000118 section not found in catalog.")
        
        section_text = jsp_section_match.group(0)
        bounty_match = re.search(r"\|\s*Historical bounty\s*\|\s*(.*?)\s*\|", section_text)
        self.assertIsNotNone(bounty_match, "Historical bounty row not found in JSP-000118.")
        
        bounty_val = bounty_match.group(1).strip()
        self.assertTrue(bounty_val.startswith("&#36;50"), f"Expected bounty to start with &#36;50, got: {bounty_val}")
        self.assertIn("I. Praton", bounty_val, "Expected citation of I. Praton in historical bounty.")

if __name__ == "__main__":
    unittest.main()