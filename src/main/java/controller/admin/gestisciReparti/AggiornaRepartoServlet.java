package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;

import java.awt.datatransfer.DataFlavor;
import java.io.IOException;

@WebServlet("/aggiorna-reparto")
public class AggiornaRepartoServlet extends HttpServlet {
    private RepartoDAO repartoService;

    public void setRepartoDAO(RepartoDAO repartoDAO) {
        this.repartoService = repartoDAO;
    }

    public void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException, ServletException {
            String idParam = request.getParameter("idReparto");
            int id;

            try {
                id = Integer.parseInt(idParam);
            } catch (NumberFormatException ex) {
                log("Parametro 'id' non valido: " + idParam, ex);
                RequestDispatcher dispatcher=request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp");
                try {
                    dispatcher.forward(request, response);
                } catch (ServletException | IOException e) {
                    log("Errore durante il forward verso /WEB-INF/errorJsp/ErroreReparto.jsp", e);
                }
                return;
            }

            String descrizione=request.getParameter("descrizione");
            String immagine=request.getParameter("immagine");
            
            // Trim parameters to remove leading/trailing whitespace
            if(descrizione != null) descrizione = descrizione.trim();
            if(immagine != null) immagine = immagine.trim();
            
            String address="/WEB-INF/results/admin/reparti/gestisciReparti.jsp";
            if(descrizione==null || descrizione.isEmpty() || immagine==null || immagine.isEmpty()){
                    address="/WEB-INF/errorJsp/erroreForm.jsp";
            }
            else {
                    if (repartoService == null) {
                        repartoService = new RepartoDAO();
                    }
                    Reparto reparto = new Reparto();
                    reparto.setIdReparto(id);
                    reparto.setDescrizione(descrizione);
                    reparto.setImmagine(immagine);

                    repartoService.updateReparto(reparto);
            }
            RequestDispatcher dispatcher = request.getRequestDispatcher(address);
            try {
                dispatcher.forward(request, response);
            } catch (ServletException e) {
                log("Errore durante il forward ", e);
            } catch (IOException e) {
                log("Errore di I/O durante il forward", e);
            }
    }
}
