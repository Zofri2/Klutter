# Crédits et licences tierces

Klutter s'appuie sur des logiciels libres. **À vérifier avant publication** (versions et textes de licence officiels).

| Composant | Usage | Licence |
|---|---|---|
| **Qt for Python (PySide6)** | Interface | LGPL v3 (ou GPL / commerciale) |
| **NumPy** | Calculs d'image | BSD 3 clauses |
| **Python** | Langage | PSF License |
| **PyInstaller** | Création du .exe | GPL v2 avec exception pour les programmes générés |
| **Inno Setup** | Installateur | Licence Inno Setup (gratuite, y compris commerciale) |

## Obligations à respecter pour PySide6 / Qt (LGPL)
- Indique que Klutter utilise Qt et PySide6, avec un lien vers https://www.qt.io/ et https://doc.qt.io/qtforpython/.
- Joins le texte de la licence LGPL v3 (https://www.gnu.org/licenses/lgpl-3.0.html) à ta distribution.
- Ne distribue pas Klutter dans un format qui empêche de remplacer les bibliothèques Qt : l'installateur en dossier (non « un seul fichier ») avec les DLL Qt séparées le permet. Évite d'interdire la rétro-ingénierie *pour ces composants*.
- Ne modifie pas Qt sans publier les modifications.

## Icône
L'icône de Klutter est issue d'**Icons8** (https://icons8.com). La version gratuite exige un **lien d'attribution visible** vers Icons8 (par exemple sur ta page de téléchargement : « Icône par Icons8 »). Si tu veux t'en passer, tu peux acheter une licence Icons8 ou faire dessiner ton propre logo. Conserve la preuve de ta licence.

## Appareils photo et marques
Canon, Nikon, Sony, Adobe et Lightroom sont des marques de leurs propriétaires. Klutter n'est ni affilié ni approuvé par ces sociétés ; l'interface s'inspire seulement de l'organisation générale d'un module de développement. Évite d'utiliser le mot « Lightroom » dans le nom ou le slogan du produit (une simple mention « inspiré de » dans le texte de présentation est plus prudente).

## Remerciements
Merci aux communautés Qt, NumPy et Python.
