package controller.admin.gestisciReparti;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.*;

/**
 * Test class for AggiornaRepartoServlet
 * Tests the functionality of updating a department (Reparto) in the system
 */
class AggiornaRepartoServletTest {

    private AggiornaRepartoServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() {
        servlet = new AggiornaRepartoServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);
        repartoDAO = mock(RepartoDAO.class);
    }

    /**
     * Test successful update with all valid parameters
     * Expected: updateReparto called, forward to gestisciReparti.jsp
     */
    @Test
    void testDoGet_SuccessfulUpdate() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("1");
        when(request.getParameter("descrizione")).thenReturn("Libri di narrativa italiana e straniera");
        when(request.getParameter("immagine")).thenReturn("narrativa_updated.jpg");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        doNothing().when(repartoDAO).updateReparto(any(Reparto.class));
        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).updateReparto(argThat(reparto ->
                reparto.getIdReparto() == 1 &&
                reparto.getDescrizione().equals("Libri di narrativa italiana e straniera") &&
                reparto.getImmagine().equals("narrativa_updated.jpg")
        ));
        verify(request).getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when descrizione parameter is null
     * Expected: forward to erroreForm.jsp, no update
     */
    @Test
    void testDoGet_DescrizioneNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("2");
        when(request.getParameter("descrizione")).thenReturn(null);
        when(request.getParameter("immagine")).thenReturn("image.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when immagine parameter is null
     * Expected: forward to erroreForm.jsp, no update
     */
    @Test
    void testDoGet_ImmagineNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("3");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when both descrizione and immagine are null
     * Expected: forward to erroreForm.jsp, no update
     */
    @Test
    void testDoGet_BothParametersNull() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("4");
        when(request.getParameter("descrizione")).thenReturn(null);
        when(request.getParameter("immagine")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when descrizione is empty string
     * Expected: forward to erroreForm.jsp, no update
     */
    @Test
    void testDoGet_DescrizioneEmpty() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("5");
        when(request.getParameter("descrizione")).thenReturn("");
        when(request.getParameter("immagine")).thenReturn("image.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when immagine is empty string
     * Expected: forward to erroreForm.jsp, no update
     */
    @Test
    void testDoGet_ImmagineEmpty() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("6");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn("");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test when idReparto parameter is null
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_IdRepartoNull_ThrowsException() throws Exception {
        when(request.getParameter("idReparto")).thenReturn(null);
        when(request.getParameter("descrizione")).thenReturn("Descrizione");
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.setRepartoDAO(repartoDAO);

        assertThrows(NumberFormatException.class, () -> {
            servlet.doGet(request, response);
        });

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
    }

    /**
     * Test when idReparto is not a valid number
     * Expected: NumberFormatException
     */
    @Test
    void testDoGet_IdRepartoInvalid_ThrowsException() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("invalid");
        when(request.getParameter("descrizione")).thenReturn("Descrizione");
        when(request.getParameter("immagine")).thenReturn("image.jpg");

        servlet.setRepartoDAO(repartoDAO);

        assertThrows(NumberFormatException.class, () -> {
            servlet.doGet(request, response);
        });

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
    }

    /**
     * Test with whitespace-only descrizione (covers trim + isEmpty validation)
     * Expected: forward to erroreForm.jsp after trimming, no update
     */
    @Test
    void testDoGet_WhitespaceOnlyDescrizione() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("10");
        when(request.getParameter("descrizione")).thenReturn("   ");
        when(request.getParameter("immagine")).thenReturn("image.jpg");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test with whitespace-only immagine (covers trim + isEmpty validation)
     * Expected: forward to erroreForm.jsp after trimming, no update
     */
    @Test
    void testDoGet_WhitespaceOnlyImmagine() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("11");
        when(request.getParameter("descrizione")).thenReturn("Descrizione valida");
        when(request.getParameter("immagine")).thenReturn("   ");
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp"))
                .thenReturn(dispatcher);

        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO, never()).updateReparto(any(Reparto.class));
        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test with leading and trailing whitespace in valid parameters
     * Expected: whitespace is trimmed, update successful
     */
    @Test
    void testDoGet_TrimsWhitespaceFromValidParameters() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("14");
        when(request.getParameter("descrizione")).thenReturn("  Descrizione valida  ");
        when(request.getParameter("immagine")).thenReturn("  image.jpg  ");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        doNothing().when(repartoDAO).updateReparto(any(Reparto.class));
        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).updateReparto(argThat(reparto ->
                reparto.getDescrizione().equals("Descrizione valida") &&
                reparto.getImmagine().equals("image.jpg")
        ));
        verify(dispatcher).forward(request, response);
    }

    /**
     * Test dependency injection works correctly
     * Expected: uses injected DAO instead of creating new one
     */
    @Test
    void testDoGet_UsesDependencyInjection() throws Exception {
        when(request.getParameter("idReparto")).thenReturn("20");
        when(request.getParameter("descrizione")).thenReturn("Test descrizione");
        when(request.getParameter("immagine")).thenReturn("test.jpg");
        when(request.getRequestDispatcher("/WEB-INF/results/admin/reparti/gestisciReparti.jsp"))
                .thenReturn(dispatcher);

        doNothing().when(repartoDAO).updateReparto(any(Reparto.class));
        servlet.setRepartoDAO(repartoDAO);

        servlet.doGet(request, response);

        verify(repartoDAO).updateReparto(any(Reparto.class));
        verify(dispatcher).forward(request, response);
    }
}
