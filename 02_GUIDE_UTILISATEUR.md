# Guide d'utilisation de Klutter

## 1. Démarrer
Au lancement, l'accueil affiche le logo, une phrase qui change et des astuces. Clique sur **Ouvrir un dossier** (ou glisse un dossier dans la fenêtre). Les dossiers récents sont proposés sur l'accueil.

## 2. La grille
- Molette ou curseur de taille pour agrandir ou réduire les vignettes.
- La **barre latérale** à gauche contient les filtres (étoiles, drapeaux, couleurs), les destinations et les options de tri. **Glisse son bord droit** pour l'élargir ou la réduire ; `Ctrl+B` la masque.
- **Double-clic** (ou Entrée) sur une photo : ouverture plein écran. La flèche **←** en haut à gauche, `Échap`, `Alt+Gauche` ou le bouton « précédent » de la souris te ramènent à la grille.

## 3. Trier
| Action | Touche |
|---|---|
| Noter de 1 à 5 étoiles | `1` à `5` (`0` = aucune) |
| Augmenter / diminuer la note | `]` / `[` ou `Ctrl+↑` / `Ctrl+↓` |
| Garder / rejeter | `P` / `X` |
| Étiquette rouge, jaune, verte, bleue | `6`, `7`, `8`, `9` (re-appuyer = retirer) |
| Annuler la dernière action | `Ctrl+Z` |
| Renommer | `F2` |
| Comparer des photos | menu « Photo » |
| Diaporama | `S` |

*Les touches exactes figurent aussi dans Aide → Raccourcis clavier dans l'application.*

## 4. Destinations en un clic
Dans la barre latérale, ajoute des dossiers de destination (existant ou nouveau sous-dossier). Chaque destination a une touche. Choisis le mode **Déplacer** ou **Copier**, sélectionne tes photos, puis clique sur la destination (ou appuie sur sa touche). Les fichiers associés (xmp, jpg…) suivent. Tout est annulable avec `Ctrl+Z`.

## 5. Développer une photo
Ouvre une photo : l'écran ressemble au module Développement de Lightroom.
- **Gauche** : Navigateur, Préréglages, Historique, Destinations, Copier / Coller / Exporter.
- **Centre** : la photo, avec Avant / Après (`\` ou `B`), drapeaux, étoiles et étiquettes.
- **Droite** : Histogramme et infos EXIF, outil Recadrer, panneaux Basique, Détail et Effets.
- **Bas** : la pellicule pour passer d'une photo à l'autre (← / →).
- **Double-clic sur un curseur** : remise à zéro. Bouton **Réinitialiser** pour tout annuler.
- `Ctrl+Maj+C` / `Ctrl+Maj+V` : copier / coller les réglages (même sur toute une sélection depuis la grille).
- `Ctrl+Maj+E` : exporter en JPEG, PNG ou TIFF.
- `G` grille de composition, `H` histogramme, `L` lumières éteintes, `Tab` masquer les panneaux.

Les réglages sont **non destructifs** : ils sont stockés dans `trieur_photos.json` à côté des photos.

## 6. Paramètres
Bouton ⚙ de l'accueil : thème (sombre / clair), couleur d'accent, animations, taille des vignettes, vidage du cache.

## 7. Questions fréquentes
**Mes photos sont-elles modifiées ?** Non, jamais. Seuls les déplacements, copies et renommages que tu demandes touchent aux fichiers.

**Pourquoi la retouche d'un CR2 s'applique-t-elle à l'aperçu ?** Klutter travaille sur l'aperçu JPEG intégré au fichier RAW pour rester rapide.

**Où sont enregistrées mes notes ?** Dans `trieur_photos.json`, dans le dossier des photos. Sauvegarde-le avec elles.

**Windows bloque l'installateur.** Clique sur « Informations complémentaires » puis « Exécuter quand même » (logiciel non signé).

**Comment désinstaller ?** Paramètres Windows → Applications → Klutter.
