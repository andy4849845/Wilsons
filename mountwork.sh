fusermount -uz /home/andy/DataCentre
fusermount -uz /home/andy/Photos
fusermount -uz /home/andy/Wilsons

rclone --vfs-cache-mode full mount datacentre: /home/andy/DataCentre/ &
rclone --vfs-cache-mode full mount photos: /home/andy/Photos/ &
rclone --vfs-cache-mode full mount wilsons: /home/andy/Wilsons/ &
